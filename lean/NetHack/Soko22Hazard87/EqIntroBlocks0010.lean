import NetHack.Soko22Hazard87.EqIntroBlocks0009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro2500 (p : Pattern) (selected : d66357 p = 0) : d66604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66352 q = 0) : d66599 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66352, d66599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66352, d66599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2499 q selected
  have h2 (q : Pattern) (selected : d66353 q = 0) : d66600 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66353, d66600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66353, d66600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66354 q = 0) : d66601 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66354, d66601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66354, d66601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66355 q = 0) : d66602 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66355, d66602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66355, d66602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66356 q = 0) : d66603 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66356, d66603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66356, d66603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66357 q = 0) : d66604 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66357, d66604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66357, d66604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2501 (p : Pattern) (selected : d66360 p = 0) : d66607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d771 q = 0) : d52448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d776 q = 0) : d52453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66359 q = 0) : d66606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66359, d66606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66359, d66606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66360 q = 0) : d66607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66360, d66607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66360, d66607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2502 (p : Pattern) (selected : d66362 p = 0) : d66609 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d780 q = 0) : d52457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66361 q = 0) : d66608 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66361, d66608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66361, d66608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66362 q = 0) : d66609 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66362, d66609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66362, d66609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2503 (p : Pattern) (selected : d66367 p = 0) : d66614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66363 q = 0) : d66610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d66363, d66610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2501 q selected
    | true =>
      simp only [d66363, d66610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2502 q selected
  have h2 (q : Pattern) (selected : d66364 q = 0) : d66611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d66364, d66611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66364, d66611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66365 q = 0) : d66612 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d66365, d66612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66365, d66612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66366 q = 0) : d66613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d66366, d66613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66366, d66613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66367 q = 0) : d66614 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d66367, d66614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66367, d66614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2504 (p : Pattern) (selected : d66368 p = 0) : d66615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d771 q = 0) : d52448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d776 q = 0) : d52453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66359 q = 0) : d66606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66359, d66606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66359, d66606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66368 q = 0) : d66615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66368, d66615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d66368, d66615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2505 (p : Pattern) (selected : d66369 p = 0) : d66616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d780 q = 0) : d52457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66361 q = 0) : d66608 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66361, d66608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66361, d66608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66369 q = 0) : d66616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66369, d66616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66369, d66616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2506 (p : Pattern) (selected : d66374 p = 0) : d66621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66363 q = 0) : d66610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d66363, d66610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2501 q selected
    | true =>
      simp only [d66363, d66610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2502 q selected
  have h2 (q : Pattern) (selected : d66364 q = 0) : d66611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d66364, d66611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66364, d66611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66365 q = 0) : d66612 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d66365, d66612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66365, d66612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66366 q = 0) : d66613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d66366, d66613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66366, d66613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66370 q = 0) : d66617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d66370, d66617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2504 q selected
    | true =>
      simp only [d66370, d66617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2505 q selected
  have h6 (q : Pattern) (selected : d66371 q = 0) : d66618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d66371, d66618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66371, d66618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d66372 q = 0) : d66619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d66372, d66619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d66372, d66619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d66373 q = 0) : d66620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d66373, d66620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66373, d66620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d66374 q = 0) : d66621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d66374, d66621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66374, d66621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro2507 (p : Pattern) (selected : d66380 p = 0) : d66627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66375 q = 0) : d66622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d66375, d66622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2503 q selected
    | true =>
      simp only [d66375, d66622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2506 q selected
  have h2 (q : Pattern) (selected : d66376 q = 0) : d66623 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d66376, d66623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66376, d66623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d66377 q = 0) : d66624 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d66377, d66624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66377, d66624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66378 q = 0) : d66625 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d66378, d66625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66378, d66625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66379 q = 0) : d66626 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66379, d66626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66379, d66626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66380 q = 0) : d66627 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66380, d66627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66380, d66627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2508 (p : Pattern) (selected : d66386 p = 0) : d66633 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66381 q = 0) : d66628 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66381, d66628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66381, d66628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2507 q selected
  have h2 (q : Pattern) (selected : d66382 q = 0) : d66629 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66382, d66629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66382, d66629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66383 q = 0) : d66630 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66383, d66630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66383, d66630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66384 q = 0) : d66631 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66384, d66631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66384, d66631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66385 q = 0) : d66632 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66385, d66632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66385, d66632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66386 q = 0) : d66633 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66386, d66633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66386, d66633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2509 (p : Pattern) (selected : d66390 p = 0) : d66637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1150 q = 0) : d52731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1155 q = 0) : d52736 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66389 q = 0) : d66636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66389, d66636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66389, d66636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66390 q = 0) : d66637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66390, d66637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66390, d66637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2510 (p : Pattern) (selected : d66392 p = 0) : d66639 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1159 q = 0) : d52740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66391 q = 0) : d66638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66391, d66638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66391, d66638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66392 q = 0) : d66639 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66392, d66639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66392, d66639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2511 (p : Pattern) (selected : d66397 p = 0) : d66644 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66393 q = 0) : d66640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d66393, d66640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2509 q selected
    | true =>
      simp only [d66393, d66640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2510 q selected
  have h2 (q : Pattern) (selected : d66394 q = 0) : d66641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d66394, d66641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66394, d66641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66395 q = 0) : d66642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d66395, d66642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66395, d66642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66396 q = 0) : d66643 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d66396, d66643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66396, d66643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66397 q = 0) : d66644 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d66397, d66644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66397, d66644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2512 (p : Pattern) (selected : d66398 p = 0) : d66645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1150 q = 0) : d52731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1155 q = 0) : d52736 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66389 q = 0) : d66636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66389, d66636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66389, d66636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66398 q = 0) : d66645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66398, d66645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d66398, d66645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2513 (p : Pattern) (selected : d66399 p = 0) : d66646 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1159 q = 0) : d52740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66391 q = 0) : d66638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66391, d66638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66391, d66638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66399 q = 0) : d66646 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66399, d66646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66399, d66646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2514 (p : Pattern) (selected : d66404 p = 0) : d66651 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66393 q = 0) : d66640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d66393, d66640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2509 q selected
    | true =>
      simp only [d66393, d66640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2510 q selected
  have h2 (q : Pattern) (selected : d66394 q = 0) : d66641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d66394, d66641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66394, d66641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66395 q = 0) : d66642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d66395, d66642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66395, d66642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66396 q = 0) : d66643 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d66396, d66643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66396, d66643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66400 q = 0) : d66647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d66400, d66647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2512 q selected
    | true =>
      simp only [d66400, d66647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2513 q selected
  have h6 (q : Pattern) (selected : d66401 q = 0) : d66648 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d66401, d66648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66401, d66648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d66402 q = 0) : d66649 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d66402, d66649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d66402, d66649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d66403 q = 0) : d66650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d66403, d66650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66403, d66650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d66404 q = 0) : d66651 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d66404, d66651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66404, d66651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro2515 (p : Pattern) (selected : d66410 p = 0) : d66657 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66405 q = 0) : d66652 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d66405, d66652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2511 q selected
    | true =>
      simp only [d66405, d66652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2514 q selected
  have h2 (q : Pattern) (selected : d66406 q = 0) : d66653 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d66406, d66653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66406, d66653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d66407 q = 0) : d66654 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d66407, d66654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66407, d66654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66408 q = 0) : d66655 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d66408, d66655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66408, d66655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66409 q = 0) : d66656 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66409, d66656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66409, d66656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66410 q = 0) : d66657 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66410, d66657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66410, d66657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2516 (p : Pattern) (selected : d66416 p = 0) : d66663 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66411 q = 0) : d66658 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66411, d66658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66411, d66658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2515 q selected
  have h2 (q : Pattern) (selected : d66412 q = 0) : d66659 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66412, d66659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66412, d66659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66413 q = 0) : d66660 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66413, d66660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66413, d66660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66414 q = 0) : d66661 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66414, d66661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66414, d66661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66415 q = 0) : d66662 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66415, d66662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66415, d66662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66416 q = 0) : d66663 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66416, d66663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66416, d66663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2517 (p : Pattern) (selected : d66421 p = 0) : d66668 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1611 q = 0) : d53052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1616 q = 0) : d53057 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66420 q = 0) : d66667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66420, d66667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66420, d66667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66421 q = 0) : d66668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66421, d66668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66421, d66668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2518 (p : Pattern) (selected : d66423 p = 0) : d66670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1620 q = 0) : d53061 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66422 q = 0) : d66669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66422, d66669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66422, d66669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66423 q = 0) : d66670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66423, d66670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66423, d66670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2519 (p : Pattern) (selected : d66428 p = 0) : d66675 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66424 q = 0) : d66671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d66424, d66671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2517 q selected
    | true =>
      simp only [d66424, d66671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2518 q selected
  have h2 (q : Pattern) (selected : d66425 q = 0) : d66672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d66425, d66672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66425, d66672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66426 q = 0) : d66673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d66426, d66673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66426, d66673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66427 q = 0) : d66674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d66427, d66674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66427, d66674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66428 q = 0) : d66675 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d66428, d66675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66428, d66675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2520 (p : Pattern) (selected : d66429 p = 0) : d66676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1611 q = 0) : d53052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1616 q = 0) : d53057 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66420 q = 0) : d66667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66420, d66667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66420, d66667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66429 q = 0) : d66676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66429, d66676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d66429, d66676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2521 (p : Pattern) (selected : d66430 p = 0) : d66677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1620 q = 0) : d53061 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66422 q = 0) : d66669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66422, d66669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66422, d66669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66430 q = 0) : d66677 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66430, d66677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66430, d66677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2522 (p : Pattern) (selected : d66435 p = 0) : d66682 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66424 q = 0) : d66671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d66424, d66671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2517 q selected
    | true =>
      simp only [d66424, d66671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2518 q selected
  have h2 (q : Pattern) (selected : d66425 q = 0) : d66672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d66425, d66672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66425, d66672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66426 q = 0) : d66673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d66426, d66673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66426, d66673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66427 q = 0) : d66674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d66427, d66674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66427, d66674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66431 q = 0) : d66678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d66431, d66678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2520 q selected
    | true =>
      simp only [d66431, d66678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2521 q selected
  have h6 (q : Pattern) (selected : d66432 q = 0) : d66679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d66432, d66679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66432, d66679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d66433 q = 0) : d66680 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d66433, d66680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d66433, d66680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d66434 q = 0) : d66681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d66434, d66681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66434, d66681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d66435 q = 0) : d66682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d66435, d66682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66435, d66682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro2523 (p : Pattern) (selected : d66441 p = 0) : d66688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66436 q = 0) : d66683 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d66436, d66683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2519 q selected
    | true =>
      simp only [d66436, d66683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2522 q selected
  have h2 (q : Pattern) (selected : d66437 q = 0) : d66684 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d66437, d66684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66437, d66684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d66438 q = 0) : d66685 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d66438, d66685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66438, d66685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66439 q = 0) : d66686 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d66439, d66686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66439, d66686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66440 q = 0) : d66687 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66440, d66687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66440, d66687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66441 q = 0) : d66688 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66441, d66688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66441, d66688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2524 (p : Pattern) (selected : d66447 p = 0) : d66694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66442 q = 0) : d66689 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66442, d66689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66442, d66689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2523 q selected
  have h2 (q : Pattern) (selected : d66443 q = 0) : d66690 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66443, d66690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66443, d66690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66444 q = 0) : d66691 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66444, d66691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66444, d66691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66445 q = 0) : d66692 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66445, d66692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66445, d66692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66446 q = 0) : d66693 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66446, d66693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66446, d66693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66447 q = 0) : d66694 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66447, d66694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66447, d66694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2525 (p : Pattern) (selected : d66453 p = 0) : d66700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2093 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro564 q selected
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 0) : d53373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2099 q = 0) : d53378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66452 q = 0) : d66699 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66452, d66699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66452, d66699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66453 q = 0) : d66700 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66453, d66700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66453, d66700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2526 (p : Pattern) (selected : d66455 p = 0) : d66702 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2103 q = 0) : d53382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66454 q = 0) : d66701 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66454, d66701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66454, d66701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66455 q = 0) : d66702 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66455, d66702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66455, d66702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2527 (p : Pattern) (selected : d66460 p = 0) : d66707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66456 q = 0) : d66703 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d66456, d66703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2525 q selected
    | true =>
      simp only [d66456, d66703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2526 q selected
  have h2 (q : Pattern) (selected : d66457 q = 0) : d66704 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d66457, d66704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66457, d66704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66458 q = 0) : d66705 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d66458, d66705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66458, d66705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66459 q = 0) : d66706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d66459, d66706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66459, d66706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66460 q = 0) : d66707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d66460, d66707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66460, d66707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2528 (p : Pattern) (selected : d66461 p = 0) : d66708 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2093 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro564 q selected
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 0) : d53373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2099 q = 0) : d53378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66452 q = 0) : d66699 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66452, d66699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66452, d66699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66461 q = 0) : d66708 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66461, d66708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d66461, d66708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2529 (p : Pattern) (selected : d66462 p = 0) : d66709 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2103 q = 0) : d53382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66454 q = 0) : d66701 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d66454, d66701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66454, d66701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66462 q = 0) : d66709 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d66462, d66709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66462, d66709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2530 (p : Pattern) (selected : d66467 p = 0) : d66714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66456 q = 0) : d66703 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d66456, d66703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2525 q selected
    | true =>
      simp only [d66456, d66703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2526 q selected
  have h2 (q : Pattern) (selected : d66457 q = 0) : d66704 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d66457, d66704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66457, d66704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66458 q = 0) : d66705 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d66458, d66705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66458, d66705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66459 q = 0) : d66706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d66459, d66706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66459, d66706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66463 q = 0) : d66710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d66463, d66710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2528 q selected
    | true =>
      simp only [d66463, d66710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2529 q selected
  have h6 (q : Pattern) (selected : d66464 q = 0) : d66711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d66464, d66711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66464, d66711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d66465 q = 0) : d66712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d66465, d66712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d66465, d66712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d66466 q = 0) : d66713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d66466, d66713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66466, d66713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d66467 q = 0) : d66714 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d66467, d66714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66467, d66714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro2531 (p : Pattern) (selected : d66473 p = 0) : d66720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66468 q = 0) : d66715 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d66468, d66715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2527 q selected
    | true =>
      simp only [d66468, d66715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2530 q selected
  have h2 (q : Pattern) (selected : d66469 q = 0) : d66716 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d66469, d66716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66469, d66716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d66470 q = 0) : d66717 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d66470, d66717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66470, d66717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66471 q = 0) : d66718 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d66471, d66718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66471, d66718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66472 q = 0) : d66719 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66472, d66719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66472, d66719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66473 q = 0) : d66720 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66473, d66720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66473, d66720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2532 (p : Pattern) (selected : d66479 p = 0) : d66726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66474 q = 0) : d66721 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66474, d66721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66474, d66721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2531 q selected
  have h2 (q : Pattern) (selected : d66475 q = 0) : d66722 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66475, d66722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66475, d66722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66476 q = 0) : d66723 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66476, d66723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66476, d66723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66477 q = 0) : d66724 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66477, d66724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66477, d66724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66478 q = 0) : d66725 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66478, d66725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66478, d66725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66479 q = 0) : d66726 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66479, d66726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66479, d66726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2533 (p : Pattern) (selected : d66485 p = 0) : d66732 p = 1 := by
  have h0 (q : Pattern) (selected : d66358 q = 0) : d66605 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d66358, d66605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2492 q selected
    | true =>
      simp only [d66358, d66605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2500 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d66387 q = 0) : d66634 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d66387, d66634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66387, d66634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2508 q selected
  have h3 (q : Pattern) (selected : d66388 q = 0) : d66635 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d66388, d66635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66388, d66635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66417 q = 0) : d66664 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d66417, d66664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66417, d66664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2516 q selected
  have h5 (q : Pattern) (selected : d66418 q = 0) : d66665 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d66418, d66665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66418, d66665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66419 q = 0) : d66666 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d66419, d66666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66419, d66666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d66448 q = 0) : d66695 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d66448, d66695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66448, d66695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2524 q selected
  have h8 (q : Pattern) (selected : d66449 q = 0) : d66696 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d66449, d66696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66449, d66696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d66450 q = 0) : d66697 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d66450, d66697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66450, d66697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d66451 q = 0) : d66698 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d66451, d66698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d66451, d66698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d66480 q = 0) : d66727 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d66480, d66727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66480, d66727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2532 q selected
  have h12 (q : Pattern) (selected : d66481 q = 0) : d66728 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d66481, d66728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66481, d66728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d66482 q = 0) : d66729 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d66482, d66729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66482, d66729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d66483 q = 0) : d66730 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d66483, d66730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66483, d66730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d66484 q = 0) : d66731 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d66484, d66731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d66484, d66731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d66485 q = 0) : d66732 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d66485, d66732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d66485, d66732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2534 (p : Pattern) (selected : d66491 p = 0) : d66738 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66486 q = 0) : d66733 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d66486, d66733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2533 q selected
    | true =>
      simp only [d66486, d66733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d66487 q = 0) : d66734 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d66487, d66734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66487, d66734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d66488 q = 0) : d66735 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d66488, d66735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66488, d66735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66489 q = 0) : d66736 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d66489, d66736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66489, d66736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66490 q = 0) : d66737 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d66490, d66737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66490, d66737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66491 q = 0) : d66738 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d66491, d66738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66491, d66738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2535 (p : Pattern) (selected : d66497 p = 0) : d66744 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66492 q = 0) : d66739 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d66492, d66739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2534 q selected
    | true =>
      simp only [d66492, d66739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d66493 q = 0) : d66740 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d66493, d66740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66493, d66740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d66494 q = 0) : d66741 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d66494, d66741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66494, d66741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66495 q = 0) : d66742 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d66495, d66742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66495, d66742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66496 q = 0) : d66743 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d66496, d66743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66496, d66743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66497 q = 0) : d66744 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d66497, d66744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66497, d66744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2536 (p : Pattern) (selected : d66503 p = 0) : d66750 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66498 q = 0) : d66745 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d66498, d66745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2535 q selected
    | true =>
      simp only [d66498, d66745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d66499 q = 0) : d66746 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d66499, d66746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66499, d66746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d66500 q = 0) : d66747 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d66500, d66747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66500, d66747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66501 q = 0) : d66748 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d66501, d66748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66501, d66748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66502 q = 0) : d66749 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d66502, d66749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66502, d66749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66503 q = 0) : d66750 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d66503, d66750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66503, d66750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2537 (p : Pattern) (selected : d66509 p = 0) : d66756 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66504 q = 0) : d66751 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d66504, d66751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2536 q selected
    | true =>
      simp only [d66504, d66751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d66505 q = 0) : d66752 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d66505, d66752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66505, d66752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d66506 q = 0) : d66753 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d66506, d66753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66506, d66753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66507 q = 0) : d66754 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d66507, d66754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66507, d66754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66508 q = 0) : d66755 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d66508, d66755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66508, d66755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66509 q = 0) : d66756 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d66509, d66756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66509, d66756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2538 (p : Pattern) (selected : d66515 p = 0) : d66762 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66510 q = 0) : d66757 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d66510, d66757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2537 q selected
    | true =>
      simp only [d66510, d66757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d66511 q = 0) : d66758 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d66511, d66758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66511, d66758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d66512 q = 0) : d66759 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d66512, d66759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66512, d66759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66513 q = 0) : d66760 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d66513, d66760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66513, d66760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66514 q = 0) : d66761 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d66514, d66761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66514, d66761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66515 q = 0) : d66762 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d66515, d66762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66515, d66762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2539 (p : Pattern) (selected : d66521 p = 0) : d66768 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66516 q = 0) : d66763 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d66516, d66763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2538 q selected
    | true =>
      simp only [d66516, d66763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d66517 q = 0) : d66764 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d66517, d66764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66517, d66764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d66518 q = 0) : d66765 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d66518, d66765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66518, d66765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66519 q = 0) : d66766 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d66519, d66766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66519, d66766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66520 q = 0) : d66767 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d66520, d66767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66520, d66767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66521 q = 0) : d66768 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d66521, d66768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66521, d66768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2540 (p : Pattern) (selected : d66527 p = 0) : d66774 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66522 q = 0) : d66769 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d66522, d66769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2539 q selected
    | true =>
      simp only [d66522, d66769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d66523 q = 0) : d66770 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d66523, d66770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66523, d66770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d66524 q = 0) : d66771 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d66524, d66771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66524, d66771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d66525 q = 0) : d66772 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d66525, d66772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66525, d66772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d66526 q = 0) : d66773 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d66526, d66773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66526, d66773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66527 q = 0) : d66774 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d66527, d66774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d66527, d66774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2541 (p : Pattern) (selected : d66527 p = 1) : d66527 p = 1 := by
  have h0 (q : Pattern) (selected : d66527 q = 1) : d66527 q = 1 := by
    exact selected
  exact h0 p selected
theorem eqIntro2542 (p : Pattern) (selected : d66946 p = 0) : d67065 p = 1 := by
  have h0 (q : Pattern) (selected : d56 q = 0) : d51908 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, d51908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro191 q selected
    | true =>
      simp only [d56, d51908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro193 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d57 q = 0) : d51909 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, d51909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57, d51909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66945 q = 0) : d67064 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66945, d67064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66945, d67064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d66946 q = 0) : d67065 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66946, d67065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66946, d67065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro2543 (p : Pattern) (selected : d66952 p = 0) : d67071 p = 1 := by
  have h0 (q : Pattern) (selected : d212 q = 0) : d52030 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212, d52030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro214 q selected
    | true =>
      simp only [d212, d52030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro219 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d214 q = 0) : d52032 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro220 q selected
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d215 q = 0) : d52033 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d215, d52033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d215, d52033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66951 q = 0) : d67070 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66951, d67070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66951, d67070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d66952 q = 0) : d67071 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66952, d67071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66952, d67071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro2544 (p : Pattern) (selected : d66959 p = 0) : d67078 p = 1 := by
  have h0 (q : Pattern) (selected : d396 q = 0) : d52162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d396, d52162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro244 q selected
    | true =>
      simp only [d396, d52162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro249 q selected
  have h1 (q : Pattern) (selected : d398 q = 0) : d52164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d52164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro250 q selected
    | true =>
      simp only [d398, d52164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro201 q selected
  have h2 (q : Pattern) (selected : d399 q = 0) : d52165 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d399, d52165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d399, d52165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h4 (q : Pattern) (selected : d66958 q = 0) : d67077 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66958, d67077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66958, d67077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66959 q = 0) : d67078 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66959, d67078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66959, d67078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2545 (p : Pattern) (selected : d66965 p = 0) : d67084 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66947 q = 0) : d67066 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66947, d67066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66947, d67066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2542 q selected
  have h2 (q : Pattern) (selected : d66948 q = 0) : d67067 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66948, d67067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66948, d67067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66949 q = 0) : d67068 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66949, d67068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66949, d67068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66950 q = 0) : d67069 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66950, d67069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66950, d67069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66953 q = 0) : d67072 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66953, d67072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66953, d67072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2543 q selected
  have h6 (q : Pattern) (selected : d66954 q = 0) : d67073 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66954, d67073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66954, d67073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d66955 q = 0) : d67074 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66955, d67074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66955, d67074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d66956 q = 0) : d67075 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66956, d67075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66956, d67075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d66957 q = 0) : d67076 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66957, d67076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66957, d67076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d66960 q = 0) : d67079 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66960, d67079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66960, d67079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2544 q selected
  have h11 (q : Pattern) (selected : d66961 q = 0) : d67080 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66961, d67080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66961, d67080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d66962 q = 0) : d67081 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66962, d67081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66962, d67081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d66963 q = 0) : d67082 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66963, d67082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66963, d67082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d66964 q = 0) : d67083 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66964, d67083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66964, d67083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d66965 q = 0) : d67084 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66965, d67084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d66965, d67084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2546 (p : Pattern) (selected : d66967 p = 0) : d67086 p = 1 := by
  have h0 (q : Pattern) (selected : d632 q = 0) : d52336 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d632, d52336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro288 q selected
    | true =>
      simp only [d632, d52336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro296 q selected
  have h1 (q : Pattern) (selected : d645 q = 0) : d52349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d52349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro297 q selected
    | true =>
      simp only [d645, d52349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro298 q selected
  have h2 (q : Pattern) (selected : d646 q = 0) : d52350 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d646, d52350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d646, d52350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h4 (q : Pattern) (selected : d66966 q = 0) : d67085 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66966, d67085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66966, d67085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66967 q = 0) : d67086 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66967, d67086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66967, d67086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2547 (p : Pattern) (selected : d66973 p = 0) : d67092 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66968 q = 0) : d67087 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66968, d67087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66968, d67087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2546 q selected
  have h2 (q : Pattern) (selected : d66969 q = 0) : d67088 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66969, d67088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66969, d67088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66970 q = 0) : d67089 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66970, d67089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66970, d67089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66971 q = 0) : d67090 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66971, d67090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66971, d67090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66972 q = 0) : d67091 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66972, d67091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66972, d67091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66973 q = 0) : d67092 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66973, d67092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66973, d67092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2548 (p : Pattern) (selected : d66976 p = 0) : d67095 p = 1 := by
  have h0 (q : Pattern) (selected : d938 q = 0) : d52557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d938, d52557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro350 q selected
    | true =>
      simp only [d938, d52557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro358 q selected
  have h1 (q : Pattern) (selected : d951 q = 0) : d52570 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro359 q selected
    | true =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro360 q selected
  have h2 (q : Pattern) (selected : d952 q = 0) : d52571 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d952, d52571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d952, d52571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h4 (q : Pattern) (selected : d66975 q = 0) : d67094 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66975, d67094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66975, d67094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66976 q = 0) : d67095 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66976, d67095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66976, d67095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2549 (p : Pattern) (selected : d66982 p = 0) : d67101 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66977 q = 0) : d67096 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66977, d67096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66977, d67096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2548 q selected
  have h2 (q : Pattern) (selected : d66978 q = 0) : d67097 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66978, d67097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66978, d67097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66979 q = 0) : d67098 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66979, d67098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66979, d67098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66980 q = 0) : d67099 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66980, d67099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66980, d67099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66981 q = 0) : d67100 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66981, d67100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66981, d67100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66982 q = 0) : d67101 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66982, d67101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66982, d67101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2550 (p : Pattern) (selected : d66986 p = 0) : d67105 p = 1 := by
  have h0 (q : Pattern) (selected : d1349 q = 0) : d52837 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1349, d52837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro426 q selected
    | true =>
      simp only [d1349, d52837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro434 q selected
  have h1 (q : Pattern) (selected : d1362 q = 0) : d52850 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro435 q selected
    | true =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro436 q selected
  have h2 (q : Pattern) (selected : d1363 q = 0) : d52851 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1363, d52851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1363, d52851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h4 (q : Pattern) (selected : d66985 q = 0) : d67104 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66985, d67104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66985, d67104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66986 q = 0) : d67105 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66986, d67105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66986, d67105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2551 (p : Pattern) (selected : d66992 p = 0) : d67111 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66987 q = 0) : d67106 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66987, d67106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66987, d67106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2550 q selected
  have h2 (q : Pattern) (selected : d66988 q = 0) : d67107 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66988, d67107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66988, d67107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66989 q = 0) : d67108 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66989, d67108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66989, d67108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66990 q = 0) : d67109 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66990, d67109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66990, d67109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66991 q = 0) : d67110 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66991, d67110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66991, d67110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66992 q = 0) : d67111 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66992, d67111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66992, d67111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2552 (p : Pattern) (selected : d66997 p = 0) : d67116 p = 1 := by
  have h0 (q : Pattern) (selected : d1826 q = 0) : d53152 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1826, d53152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro512 q selected
    | true =>
      simp only [d1826, d53152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro520 q selected
  have h1 (q : Pattern) (selected : d1839 q = 0) : d53165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro521 q selected
    | true =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro522 q selected
  have h2 (q : Pattern) (selected : d1840 q = 0) : d53166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1840, d53166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1840, d53166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h4 (q : Pattern) (selected : d66996 q = 0) : d67115 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66996, d67115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66996, d67115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66997 q = 0) : d67116 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66997, d67116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66997, d67116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2553 (p : Pattern) (selected : d67003 p = 0) : d67122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66998 q = 0) : d67117 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66998, d67117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66998, d67117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2552 q selected
  have h2 (q : Pattern) (selected : d66999 q = 0) : d67118 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66999, d67118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66999, d67118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d67000 q = 0) : d67119 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67000, d67119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67000, d67119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d67001 q = 0) : d67120 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67001, d67120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67001, d67120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d67002 q = 0) : d67121 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67002, d67121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67002, d67121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d67003 q = 0) : d67122 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67003, d67122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67003, d67122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2554 (p : Pattern) (selected : d67009 p = 0) : d67128 p = 1 := by
  have h0 (q : Pattern) (selected : d2304 q = 0) : d53469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2304, d53469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro602 q selected
    | true =>
      simp only [d2304, d53469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro610 q selected
  have h1 (q : Pattern) (selected : d2317 q = 0) : d53482 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro611 q selected
    | true =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro612 q selected
  have h2 (q : Pattern) (selected : d2318 q = 0) : d53483 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2318, d53483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2318, d53483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h4 (q : Pattern) (selected : d67008 q = 0) : d67127 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67008, d67127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67008, d67127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d67009 q = 0) : d67128 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67009, d67128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67009, d67128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2555 (p : Pattern) (selected : d67015 p = 0) : d67134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d67010 q = 0) : d67129 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67010, d67129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67010, d67129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2554 q selected
  have h2 (q : Pattern) (selected : d67011 q = 0) : d67130 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67011, d67130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67011, d67130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d67012 q = 0) : d67131 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67012, d67131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67012, d67131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d67013 q = 0) : d67132 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67013, d67132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67013, d67132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d67014 q = 0) : d67133 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67014, d67133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67014, d67133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d67015 q = 0) : d67134 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67015, d67134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67015, d67134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2556 (p : Pattern) (selected : d67021 p = 0) : d67140 p = 1 := by
  have h0 (q : Pattern) (selected : d66974 q = 0) : d67093 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d66974, d67093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2545 q selected
    | true =>
      simp only [d66974, d67093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2547 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d66983 q = 0) : d67102 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d66983, d67102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66983, d67102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2549 q selected
  have h3 (q : Pattern) (selected : d66984 q = 0) : d67103 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d66984, d67103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66984, d67103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66993 q = 0) : d67112 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d66993, d67112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66993, d67112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2551 q selected
  have h5 (q : Pattern) (selected : d66994 q = 0) : d67113 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d66994, d67113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66994, d67113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66995 q = 0) : d67114 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d66995, d67114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66995, d67114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d67004 q = 0) : d67123 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67004, d67123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67004, d67123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2553 q selected
  have h8 (q : Pattern) (selected : d67005 q = 0) : d67124 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67005, d67124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67005, d67124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d67006 q = 0) : d67125 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67006, d67125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67006, d67125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d67007 q = 0) : d67126 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d67007, d67126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d67007, d67126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d67016 q = 0) : d67135 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67016, d67135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67016, d67135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2555 q selected
  have h12 (q : Pattern) (selected : d67017 q = 0) : d67136 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67017, d67136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67017, d67136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d67018 q = 0) : d67137 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67018, d67137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67018, d67137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d67019 q = 0) : d67138 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d67019, d67138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67019, d67138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d67020 q = 0) : d67139 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d67020, d67139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d67020, d67139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d67021 q = 0) : d67140 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d67021, d67140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d67021, d67140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2557 (p : Pattern) (selected : d67027 p = 0) : d67146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d67022 q = 0) : d67141 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d67022, d67141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2556 q selected
    | true =>
      simp only [d67022, d67141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67023 q = 0) : d67142 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d67023, d67142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67023, d67142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67024 q = 0) : d67143 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d67024, d67143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67024, d67143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67025 q = 0) : d67144 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d67025, d67144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67025, d67144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67026 q = 0) : d67145 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d67026, d67145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67026, d67145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67027 q = 0) : d67146 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d67027, d67146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67027, d67146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2558 (p : Pattern) (selected : d67033 p = 0) : d67152 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d67028 q = 0) : d67147 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d67028, d67147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2557 q selected
    | true =>
      simp only [d67028, d67147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67029 q = 0) : d67148 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d67029, d67148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67029, d67148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67030 q = 0) : d67149 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d67030, d67149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67030, d67149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67031 q = 0) : d67150 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d67031, d67150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67031, d67150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67032 q = 0) : d67151 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d67032, d67151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67032, d67151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67033 q = 0) : d67152 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d67033, d67152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67033, d67152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2559 (p : Pattern) (selected : d67039 p = 0) : d67158 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d67034 q = 0) : d67153 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d67034, d67153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2558 q selected
    | true =>
      simp only [d67034, d67153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67035 q = 0) : d67154 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d67035, d67154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67035, d67154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67036 q = 0) : d67155 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d67036, d67155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67036, d67155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67037 q = 0) : d67156 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d67037, d67156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67037, d67156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67038 q = 0) : d67157 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d67038, d67157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67038, d67157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67039 q = 0) : d67158 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d67039, d67158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67039, d67158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2560 (p : Pattern) (selected : d67045 p = 0) : d67164 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d67040 q = 0) : d67159 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d67040, d67159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2559 q selected
    | true =>
      simp only [d67040, d67159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67041 q = 0) : d67160 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d67041, d67160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67041, d67160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67042 q = 0) : d67161 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d67042, d67161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67042, d67161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67043 q = 0) : d67162 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d67043, d67162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67043, d67162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67044 q = 0) : d67163 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d67044, d67163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67044, d67163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67045 q = 0) : d67164 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d67045, d67164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67045, d67164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2561 (p : Pattern) (selected : d67051 p = 0) : d67170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d67046 q = 0) : d67165 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d67046, d67165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2560 q selected
    | true =>
      simp only [d67046, d67165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67047 q = 0) : d67166 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d67047, d67166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67047, d67166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67048 q = 0) : d67167 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d67048, d67167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67048, d67167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67049 q = 0) : d67168 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d67049, d67168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67049, d67168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67050 q = 0) : d67169 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d67050, d67169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67050, d67169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67051 q = 0) : d67170 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d67051, d67170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67051, d67170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2562 (p : Pattern) (selected : d67057 p = 0) : d67176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d67052 q = 0) : d67171 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d67052, d67171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2561 q selected
    | true =>
      simp only [d67052, d67171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67053 q = 0) : d67172 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d67053, d67172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67053, d67172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67054 q = 0) : d67173 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d67054, d67173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67054, d67173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67055 q = 0) : d67174 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d67055, d67174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67055, d67174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67056 q = 0) : d67175 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d67056, d67175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67056, d67175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67057 q = 0) : d67176 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d67057, d67176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67057, d67176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2563 (p : Pattern) (selected : d67063 p = 0) : d67182 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d67058 q = 0) : d67177 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d67058, d67177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2562 q selected
    | true =>
      simp only [d67058, d67177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67059 q = 0) : d67178 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d67059, d67178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67059, d67178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67060 q = 0) : d67179 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d67060, d67179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67060, d67179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67061 q = 0) : d67180 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d67061, d67180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67061, d67180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67062 q = 0) : d67181 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d67062, d67181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67062, d67181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67063 q = 0) : d67182 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d67063, d67182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67063, d67182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2564 (p : Pattern) (selected : d66952 p = 1) : d67184 p = 1 := by
  have h0 (q : Pattern) (selected : d212 q = 1) : d51647 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212, d51647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5 q selected
    | true =>
      simp only [d212, d51647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7 q selected
  have h1 (q : Pattern) (selected : d214 q = 1) : d214 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d215 q = 1) : d51648 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d215, d51648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d215, d51648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d66951 q = 1) : d67183 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66951, d67183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66951, d67183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66952 q = 1) : d67184 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66952, d67184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66952, d67184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2565 (p : Pattern) (selected : d66959 p = 1) : d67191 p = 1 := by
  have h0 (q : Pattern) (selected : d396 q = 1) : d51664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d396, d51664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19 q selected
    | true =>
      simp only [d396, d51664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21 q selected
  have h1 (q : Pattern) (selected : d398 q = 1) : d398 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d399 q = 1) : d51665 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d399, d51665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d399, d51665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d66958 q = 1) : d67190 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66958, d67190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66958, d67190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66959 q = 1) : d67191 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66959, d67191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66959, d67191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2566 (p : Pattern) (selected : d66965 p = 1) : d67197 p = 1 := by
  have h0 (q : Pattern) (selected : d66950 q = 1) : d66950 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d66953 q = 1) : d67185 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66953, d67185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66953, d67185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2564 q selected
  have h3 (q : Pattern) (selected : d66954 q = 1) : d67186 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66954, d67186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66954, d67186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66955 q = 1) : d67187 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66955, d67187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66955, d67187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66956 q = 1) : d67188 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66956, d67188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66956, d67188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66957 q = 1) : d67189 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66957, d67189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66957, d67189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d66960 q = 1) : d67192 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66960, d67192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66960, d67192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2565 q selected
  have h8 (q : Pattern) (selected : d66961 q = 1) : d67193 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66961, d67193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66961, d67193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d66962 q = 1) : d67194 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66962, d67194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66962, d67194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d66963 q = 1) : d67195 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66963, d67195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66963, d67195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d66964 q = 1) : d67196 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66964, d67196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66964, d67196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d66965 q = 1) : d67197 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66965, d67197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d66965, d67197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro2567 (p : Pattern) (selected : d66967 p = 1) : d67199 p = 1 := by
  have h0 (q : Pattern) (selected : d632 q = 1) : d51689 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d632, d51689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36 q selected
    | true =>
      simp only [d632, d51689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39 q selected
  have h1 (q : Pattern) (selected : d645 q = 1) : d645 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d646 q = 1) : d51690 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d646, d51690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d646, d51690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d66966 q = 1) : d67198 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66966, d67198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66966, d67198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66967 q = 1) : d67199 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66967, d67199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66967, d67199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2568 (p : Pattern) (selected : d66973 p = 1) : d67205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d66968 q = 1) : d67200 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66968, d67200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66968, d67200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2567 q selected
  have h2 (q : Pattern) (selected : d66969 q = 1) : d67201 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66969, d67201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66969, d67201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66970 q = 1) : d67202 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66970, d67202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66970, d67202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66971 q = 1) : d67203 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66971, d67203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66971, d67203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66972 q = 1) : d67204 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66972, d67204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66972, d67204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66973 q = 1) : d67205 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66973, d67205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66973, d67205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2569 (p : Pattern) (selected : d66976 p = 1) : d67208 p = 1 := by
  have h0 (q : Pattern) (selected : d938 q = 1) : d51715 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d938, d51715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro60 q selected
    | true =>
      simp only [d938, d51715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro63 q selected
  have h1 (q : Pattern) (selected : d951 q = 1) : d951 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d952 q = 1) : d51716 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d952, d51716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d952, d51716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d66975 q = 1) : d67207 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66975, d67207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66975, d67207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66976 q = 1) : d67208 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66976, d67208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66976, d67208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2570 (p : Pattern) (selected : d66982 p = 1) : d67214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d66977 q = 1) : d67209 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66977, d67209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66977, d67209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2569 q selected
  have h2 (q : Pattern) (selected : d66978 q = 1) : d67210 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66978, d67210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66978, d67210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66979 q = 1) : d67211 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66979, d67211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66979, d67211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66980 q = 1) : d67212 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66980, d67212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66980, d67212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66981 q = 1) : d67213 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66981, d67213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66981, d67213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66982 q = 1) : d67214 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66982, d67214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66982, d67214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2571 (p : Pattern) (selected : d66986 p = 1) : d67218 p = 1 := by
  have h0 (q : Pattern) (selected : d1349 q = 1) : d51742 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1349, d51742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro90 q selected
    | true =>
      simp only [d1349, d51742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro93 q selected
  have h1 (q : Pattern) (selected : d1362 q = 1) : d1362 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1363 q = 1) : d51743 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1363, d51743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1363, d51743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d66985 q = 1) : d67217 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66985, d67217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66985, d67217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66986 q = 1) : d67218 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66986, d67218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66986, d67218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2572 (p : Pattern) (selected : d66992 p = 1) : d67224 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d66987 q = 1) : d67219 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66987, d67219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66987, d67219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2571 q selected
  have h2 (q : Pattern) (selected : d66988 q = 1) : d67220 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66988, d67220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66988, d67220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d66989 q = 1) : d67221 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d66989, d67221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66989, d67221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66990 q = 1) : d67222 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d66990, d67222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66990, d67222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66991 q = 1) : d67223 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d66991, d67223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66991, d67223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66992 q = 1) : d67224 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d66992, d67224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66992, d67224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2573 (p : Pattern) (selected : d66997 p = 1) : d67229 p = 1 := by
  have h0 (q : Pattern) (selected : d1826 q = 1) : d51770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1826, d51770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro126 q selected
    | true =>
      simp only [d1826, d51770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro129 q selected
  have h1 (q : Pattern) (selected : d1839 q = 1) : d1839 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1840 q = 1) : d51771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1840, d51771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1840, d51771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d66996 q = 1) : d67228 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d66996, d67228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d66996, d67228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d66997 q = 1) : d67229 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d66997, d67229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d66997, d67229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2574 (p : Pattern) (selected : d67003 p = 1) : d67235 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d66998 q = 1) : d67230 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d66998, d67230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66998, d67230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2573 q selected
  have h2 (q : Pattern) (selected : d66999 q = 1) : d67231 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d66999, d67231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66999, d67231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d67000 q = 1) : d67232 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67000, d67232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67000, d67232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d67001 q = 1) : d67233 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67001, d67233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67001, d67233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d67002 q = 1) : d67234 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67002, d67234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67002, d67234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d67003 q = 1) : d67235 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67003, d67235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67003, d67235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2575 (p : Pattern) (selected : d67009 p = 1) : d67241 p = 1 := by
  have h0 (q : Pattern) (selected : d2304 q = 1) : d51799 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2304, d51799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro163 q selected
    | true =>
      simp only [d2304, d51799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro166 q selected
  have h1 (q : Pattern) (selected : d2317 q = 1) : d2317 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2318 q = 1) : d51800 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2318, d51800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2318, d51800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d67008 q = 1) : d67240 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67008, d67240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67008, d67240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d67009 q = 1) : d67241 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67009, d67241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67009, d67241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2576 (p : Pattern) (selected : d67015 p = 1) : d67247 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d67010 q = 1) : d67242 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67010, d67242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67010, d67242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2575 q selected
  have h2 (q : Pattern) (selected : d67011 q = 1) : d67243 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67011, d67243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67011, d67243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d67012 q = 1) : d67244 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67012, d67244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67012, d67244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d67013 q = 1) : d67245 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67013, d67245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67013, d67245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d67014 q = 1) : d67246 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67014, d67246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67014, d67246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d67015 q = 1) : d67247 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67015, d67247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d67015, d67247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2577 (p : Pattern) (selected : d67021 p = 1) : d67253 p = 1 := by
  have h0 (q : Pattern) (selected : d66974 q = 1) : d67206 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d66974, d67206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2566 q selected
    | true =>
      simp only [d66974, d67206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2568 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d66983 q = 1) : d67215 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d66983, d67215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66983, d67215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2570 q selected
  have h3 (q : Pattern) (selected : d66984 q = 1) : d67216 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d66984, d67216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66984, d67216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d66993 q = 1) : d67225 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d66993, d67225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66993, d67225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2572 q selected
  have h5 (q : Pattern) (selected : d66994 q = 1) : d67226 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d66994, d67226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d66994, d67226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66995 q = 1) : d67227 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d66995, d67227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d66995, d67227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d67004 q = 1) : d67236 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67004, d67236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67004, d67236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2574 q selected
  have h8 (q : Pattern) (selected : d67005 q = 1) : d67237 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67005, d67237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67005, d67237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d67006 q = 1) : d67238 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67006, d67238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67006, d67238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d67007 q = 1) : d67239 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d67007, d67239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d67007, d67239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d67016 q = 1) : d67248 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67016, d67248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67016, d67248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2576 q selected
  have h12 (q : Pattern) (selected : d67017 q = 1) : d67249 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67017, d67249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67017, d67249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d67018 q = 1) : d67250 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67018, d67250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67018, d67250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d67019 q = 1) : d67251 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d67019, d67251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67019, d67251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d67020 q = 1) : d67252 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d67020, d67252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d67020, d67252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d67021 q = 1) : d67253 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d67021, d67253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d67021, d67253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2578 (p : Pattern) (selected : d67027 p = 1) : d67259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d67022 q = 1) : d67254 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d67022, d67254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2577 q selected
    | true =>
      simp only [d67022, d67254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67023 q = 1) : d67255 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d67023, d67255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67023, d67255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67024 q = 1) : d67256 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d67024, d67256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67024, d67256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67025 q = 1) : d67257 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d67025, d67257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67025, d67257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67026 q = 1) : d67258 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d67026, d67258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67026, d67258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67027 q = 1) : d67259 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d67027, d67259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67027, d67259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2579 (p : Pattern) (selected : d67033 p = 1) : d67265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d67028 q = 1) : d67260 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d67028, d67260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2578 q selected
    | true =>
      simp only [d67028, d67260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67029 q = 1) : d67261 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d67029, d67261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67029, d67261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67030 q = 1) : d67262 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d67030, d67262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67030, d67262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67031 q = 1) : d67263 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d67031, d67263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67031, d67263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67032 q = 1) : d67264 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d67032, d67264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67032, d67264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67033 q = 1) : d67265 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d67033, d67265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67033, d67265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2580 (p : Pattern) (selected : d67039 p = 1) : d67271 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d67034 q = 1) : d67266 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d67034, d67266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2579 q selected
    | true =>
      simp only [d67034, d67266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67035 q = 1) : d67267 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d67035, d67267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67035, d67267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67036 q = 1) : d67268 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d67036, d67268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67036, d67268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67037 q = 1) : d67269 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d67037, d67269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67037, d67269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67038 q = 1) : d67270 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d67038, d67270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67038, d67270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67039 q = 1) : d67271 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d67039, d67271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67039, d67271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2581 (p : Pattern) (selected : d67045 p = 1) : d67277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d67040 q = 1) : d67272 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d67040, d67272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2580 q selected
    | true =>
      simp only [d67040, d67272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67041 q = 1) : d67273 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d67041, d67273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67041, d67273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67042 q = 1) : d67274 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d67042, d67274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67042, d67274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67043 q = 1) : d67275 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d67043, d67275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67043, d67275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67044 q = 1) : d67276 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d67044, d67276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67044, d67276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67045 q = 1) : d67277 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d67045, d67277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67045, d67277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2582 (p : Pattern) (selected : d67051 p = 1) : d67283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d67046 q = 1) : d67278 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d67046, d67278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2581 q selected
    | true =>
      simp only [d67046, d67278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67047 q = 1) : d67279 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d67047, d67279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67047, d67279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67048 q = 1) : d67280 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d67048, d67280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67048, d67280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67049 q = 1) : d67281 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d67049, d67281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67049, d67281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67050 q = 1) : d67282 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d67050, d67282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67050, d67282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67051 q = 1) : d67283 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d67051, d67283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67051, d67283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2583 (p : Pattern) (selected : d67057 p = 1) : d67289 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d67052 q = 1) : d67284 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d67052, d67284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2582 q selected
    | true =>
      simp only [d67052, d67284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67053 q = 1) : d67285 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d67053, d67285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67053, d67285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67054 q = 1) : d67286 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d67054, d67286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67054, d67286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67055 q = 1) : d67287 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d67055, d67287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67055, d67287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67056 q = 1) : d67288 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d67056, d67288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67056, d67288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67057 q = 1) : d67289 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d67057, d67289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67057, d67289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2584 (p : Pattern) (selected : d67063 p = 1) : d67295 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d67058 q = 1) : d67290 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d67058, d67290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2583 q selected
    | true =>
      simp only [d67058, d67290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d67059 q = 1) : d67291 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d67059, d67291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67059, d67291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67060 q = 1) : d67292 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d67060, d67292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d67060, d67292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d67061 q = 1) : d67293 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d67061, d67293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d67061, d67293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d67062 q = 1) : d67294 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d67062, d67294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d67062, d67294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d67063 q = 1) : d67295 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d67063, d67295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d67063, d67295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2585 (p : Pattern) (selected : d4029 p = 0) : d67305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117 q = 0) : d51969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 0) : d51970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 0) : d51971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 0) : d51972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 0) : d51976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 0) : d51977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 0) : d51978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d157 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h9 (q : Pattern) (selected : d188 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
    | true =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d189 q = 0) : d52009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d52009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d189, d52009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4026 q = 0) : d67302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4026, d67302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4026, d67302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4027 q = 0) : d67303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4027, d67303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4027, d67303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4028 q = 0) : d67304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4028, d67304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4028, d67304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4029 q = 0) : d67305 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4029, d67305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4029, d67305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro2586 (p : Pattern) (selected : d4033 p = 0) : d67309 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117 q = 0) : d51969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 0) : d51970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 0) : d51971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 0) : d51972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 0) : d51976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 0) : d51977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 0) : d51978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d157 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h9 (q : Pattern) (selected : d188 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
    | true =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d189 q = 0) : d52009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d52009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d189, d52009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4026 q = 0) : d67302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4026, d67302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4026, d67302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4027 q = 0) : d67303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4027, d67303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4027, d67303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4028 q = 0) : d67304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4028, d67304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4028, d67304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d195 q = 0) : d52015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d196 q = 0) : d52016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d197 q = 0) : d52017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d198 q = 0) : d52018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d200 q = 0) : d52020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro216 q selected
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d201 q = 0) : d52021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d202 q = 0) : d52022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d204 q = 0) : d52024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h22 (q : Pattern) (selected : d206 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
    | true =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d207 q = 0) : d52025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207, d52025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d207, d52025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d4030 q = 0) : d67306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4030, d67306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d4030, d67306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d4031 q = 0) : d67307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4031, d67307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4031, d67307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d4032 q = 0) : d67308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4032, d67308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4032, d67308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d4033 q = 0) : d67309 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4033, d67309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4033, d67309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro2587 (p : Pattern) (selected : d4040 p = 0) : d67316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204 q = 0) : d52024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h2 (q : Pattern) (selected : d206 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
    | true =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d207 q = 0) : d52025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207, d52025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d207, d52025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4030 q = 0) : d67306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4030, d67306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4030, d67306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4038 q = 0) : d67314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4038, d67314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4038, d67314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4039 q = 0) : d67315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4039, d67315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4039, d67315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4040 q = 0) : d67316 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4040, d67316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4040, d67316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2588 (p : Pattern) (selected : d4049 p = 0) : d67325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d244 q = 0) : d52062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d52062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro224 q selected
    | true =>
      simp only [d244, d52062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
  have h2 (q : Pattern) (selected : d263 q = 0) : d51936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro227 q selected
    | true =>
      simp only [d263, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d264 q = 0) : d52063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d264, d52063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d264, d52063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4046 q = 0) : d67322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4046, d67322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4046, d67322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4047 q = 0) : d67323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4047, d67323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4047, d67323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4048 q = 0) : d67324 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4048, d67324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4048, d67324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4049 q = 0) : d67325 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4049, d67325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4049, d67325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2589 (p : Pattern) (selected : d4055 p = 0) : d67331 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105 q = 0) : d51957 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro200 q selected
  have h2 (q : Pattern) (selected : d106 q = 0) : d51958 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d112 q = 0) : d51964 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro200 q selected
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro201 q selected
  have h4 (q : Pattern) (selected : d113 q = 0) : d51965 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d114 q = 0) : d51966 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4034 q = 0) : d67310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4034, d67310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2585 q selected
    | true =>
      simp only [d4034, d67310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2586 q selected
  have h7 (q : Pattern) (selected : d214 q = 0) : d52032 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro220 q selected
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d4035 q = 0) : d67311 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4035, d67311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4035, d67311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4036 q = 0) : d67312 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4036, d67312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4036, d67312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d4037 q = 0) : d67313 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4037, d67313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4037, d67313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4041 q = 0) : d67317 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4041, d67317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4041, d67317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2587 q selected
  have h12 (q : Pattern) (selected : d4042 q = 0) : d67318 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4042, d67318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4042, d67318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d4043 q = 0) : d67319 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4043, d67319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4043, d67319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d4044 q = 0) : d67320 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4044, d67320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4044, d67320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4045 q = 0) : d67321 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4045, d67321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4045, d67321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4050 q = 0) : d67326 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4050, d67326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4050, d67326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2588 q selected
  have h17 (q : Pattern) (selected : d4051 q = 0) : d67327 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4051, d67327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4051, d67327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d4052 q = 0) : d67328 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4052, d67328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4052, d67328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d4053 q = 0) : d67329 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4053, d67329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d4053, d67329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d4054 q = 0) : d67330 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4054, d67330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d4054, d67330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d4055 q = 0) : d67331 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4055, d67331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d4055, d67331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro2590 (p : Pattern) (selected : d4064 p = 0) : d67340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d297 q = 0) : d52096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro232 q selected
    | true =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d298 q = 0) : d52097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d299 q = 0) : d52098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300 q = 0) : d52099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d304 q = 0) : d52103 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro233 q selected
    | true =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h6 (q : Pattern) (selected : d305 q = 0) : d52104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d306 q = 0) : d52105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d337 q = 0) : d52136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro238 q selected
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
  have h9 (q : Pattern) (selected : d368 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro243 q selected
    | true =>
      simp only [d368, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h10 (q : Pattern) (selected : d369 q = 0) : d52137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d52137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d369, d52137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4061 q = 0) : d67337 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4061, d67337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4061, d67337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4062 q = 0) : d67338 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4062, d67338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4062, d67338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4063 q = 0) : d67339 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4063, d67339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4063, d67339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4064 q = 0) : d67340 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4064, d67340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4064, d67340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro2591 (p : Pattern) (selected : d4068 p = 0) : d67344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d297 q = 0) : d52096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro232 q selected
    | true =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d298 q = 0) : d52097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d299 q = 0) : d52098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300 q = 0) : d52099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d304 q = 0) : d52103 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro233 q selected
    | true =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h6 (q : Pattern) (selected : d305 q = 0) : d52104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d306 q = 0) : d52105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d337 q = 0) : d52136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro238 q selected
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
  have h9 (q : Pattern) (selected : d368 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro243 q selected
    | true =>
      simp only [d368, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h10 (q : Pattern) (selected : d369 q = 0) : d52137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d52137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d369, d52137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4061 q = 0) : d67337 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4061, d67337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4061, d67337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4062 q = 0) : d67338 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4062, d67338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4062, d67338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4063 q = 0) : d67339 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4063, d67339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4063, d67339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d377 q = 0) : d52145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d52145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro245 q selected
    | true =>
      simp only [d377, d52145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
  have h15 (q : Pattern) (selected : d378 q = 0) : d52146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d52146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d378, d52146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d379 q = 0) : d52147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d52147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d379, d52147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d380 q = 0) : d52148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d52148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d380, d52148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d382 q = 0) : d52150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d52150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro246 q selected
    | true =>
      simp only [d382, d52150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro216 q selected
  have h19 (q : Pattern) (selected : d383 q = 0) : d52151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d52151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d383, d52151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d384 q = 0) : d52152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d52152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d384, d52152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d386 q = 0) : d52154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro247 q selected
    | true =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
  have h22 (q : Pattern) (selected : d388 q = 0) : d52024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d388, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro248 q selected
    | true =>
      simp only [d388, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h23 (q : Pattern) (selected : d389 q = 0) : d52155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d389, d52155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d389, d52155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d4065 q = 0) : d67341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4065, d67341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d4065, d67341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d4066 q = 0) : d67342 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4066, d67342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4066, d67342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d4067 q = 0) : d67343 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4067, d67343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4067, d67343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d4068 q = 0) : d67344 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4068, d67344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4068, d67344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro2592 (p : Pattern) (selected : d4075 p = 0) : d67351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d386 q = 0) : d52154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro247 q selected
    | true =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
  have h2 (q : Pattern) (selected : d388 q = 0) : d52024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d388, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro248 q selected
    | true =>
      simp only [d388, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h3 (q : Pattern) (selected : d389 q = 0) : d52155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d389, d52155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d389, d52155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4065 q = 0) : d67341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4065, d67341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4065, d67341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4073 q = 0) : d67349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4073, d67349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4073, d67349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4074 q = 0) : d67350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4074, d67350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4074, d67350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4075 q = 0) : d67351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4075, d67351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4075, d67351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2593 (p : Pattern) (selected : d4084 p = 0) : d67360 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d430 q = 0) : d52196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d430, d52196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro255 q selected
    | true =>
      simp only [d430, d52196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro224 q selected
  have h2 (q : Pattern) (selected : d449 q = 0) : d52062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d449, d52062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro258 q selected
    | true =>
      simp only [d449, d52062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro227 q selected
  have h3 (q : Pattern) (selected : d450 q = 0) : d52197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d450, d52197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d450, d52197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4081 q = 0) : d67357 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4081, d67357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4081, d67357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4082 q = 0) : d67358 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4082, d67358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4082, d67358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4083 q = 0) : d67359 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4083, d67359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4083, d67359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4084 q = 0) : d67360 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4084, d67360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4084, d67360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2594 (p : Pattern) (selected : d4090 p = 0) : d67366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d285 q = 0) : d52084 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro230 q selected
  have h2 (q : Pattern) (selected : d286 q = 0) : d52085 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292 q = 0) : d52091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro230 q selected
    | true =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro231 q selected
  have h4 (q : Pattern) (selected : d293 q = 0) : d52092 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d294 q = 0) : d52093 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4069 q = 0) : d67345 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4069, d67345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2590 q selected
    | true =>
      simp only [d4069, d67345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2591 q selected
  have h7 (q : Pattern) (selected : d398 q = 0) : d52164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d52164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro250 q selected
    | true =>
      simp only [d398, d52164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro201 q selected
  have h8 (q : Pattern) (selected : d4070 q = 0) : d67346 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4070, d67346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4070, d67346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4071 q = 0) : d67347 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4071, d67347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4071, d67347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d4072 q = 0) : d67348 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4072, d67348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4072, d67348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4076 q = 0) : d67352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4076, d67352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4076, d67352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2592 q selected
  have h12 (q : Pattern) (selected : d407 q = 0) : d52173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro252 q selected
  have h13 (q : Pattern) (selected : d4077 q = 0) : d67353 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4077, d67353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4077, d67353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4078 q = 0) : d67354 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4078, d67354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4078, d67354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4079 q = 0) : d67355 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4079, d67355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d4079, d67355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d4080 q = 0) : d67356 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4080, d67356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4080, d67356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4085 q = 0) : d67361 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4085, d67361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4085, d67361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2593 q selected
  have h18 (q : Pattern) (selected : d463 q = 0) : d52210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro260 q selected
  have h19 (q : Pattern) (selected : d4086 q = 0) : d67362 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4086, d67362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4086, d67362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d4087 q = 0) : d67363 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4087, d67363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d4087, d67363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d4088 q = 0) : d67364 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4088, d67364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4088, d67364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d4089 q = 0) : d67365 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4089, d67365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d4089, d67365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d4090 q = 0) : d67366 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4090, d67366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4090, d67366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro2595 (p : Pattern) (selected : d4096 p = 0) : d67372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96 q = 0) : d51948 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro199 q selected
  have h2 (q : Pattern) (selected : d97 q = 0) : d51949 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 0) : d51950 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 0) : d51951 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4056 q = 0) : d67332 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4056, d67332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4056, d67332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2589 q selected
  have h6 (q : Pattern) (selected : d4057 q = 0) : d67333 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4057, d67333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4057, d67333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4058 q = 0) : d67334 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4058, d67334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4058, d67334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4059 q = 0) : d67335 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4059, d67335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4059, d67335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4060 q = 0) : d67336 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4060, d67336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4060, d67336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4091 q = 0) : d67367 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4091, d67367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4091, d67367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2594 q selected
  have h11 (q : Pattern) (selected : d4092 q = 0) : d67368 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4092, d67368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4092, d67368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d4093 q = 0) : d67369 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4093, d67369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4093, d67369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4094 q = 0) : d67370 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4094, d67370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4094, d67370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4095 q = 0) : d67371 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4095, d67371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4095, d67371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d4096 q = 0) : d67372 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4096, d67372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4096, d67372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2596 (p : Pattern) (selected : d4100 p = 0) : d67376 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d515 q = 0) : d52262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro271 q selected
    | true =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro272 q selected
  have h2 (q : Pattern) (selected : d516 q = 0) : d52263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d517 q = 0) : d52264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d518 q = 0) : d52265 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d52265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d518, d52265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d525 q = 0) : d52272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro273 q selected
    | true =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro274 q selected
  have h6 (q : Pattern) (selected : d526 q = 0) : d52273 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d527 q = 0) : d52274 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d561 q = 0) : d52308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro280 q selected
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
  have h9 (q : Pattern) (selected : d601 q = 0) : d52239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro286 q selected
    | true =>
      simp only [d601, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro287 q selected
  have h10 (q : Pattern) (selected : d602 q = 0) : d52309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d52309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d602, d52309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4097 q = 0) : d67373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4097, d67373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4097, d67373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4098 q = 0) : d67374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4098, d67374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4098, d67374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4099 q = 0) : d67375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4099, d67375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4099, d67375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4100 q = 0) : d67376 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4100, d67376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4100, d67376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro2597 (p : Pattern) (selected : d4104 p = 0) : d67380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d515 q = 0) : d52262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro271 q selected
    | true =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro272 q selected
  have h2 (q : Pattern) (selected : d516 q = 0) : d52263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d517 q = 0) : d52264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d518 q = 0) : d52265 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d52265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d518, d52265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d525 q = 0) : d52272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro273 q selected
    | true =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro274 q selected
  have h6 (q : Pattern) (selected : d526 q = 0) : d52273 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d527 q = 0) : d52274 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d561 q = 0) : d52308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro280 q selected
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
  have h9 (q : Pattern) (selected : d601 q = 0) : d52239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro286 q selected
    | true =>
      simp only [d601, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro287 q selected
  have h10 (q : Pattern) (selected : d602 q = 0) : d52309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d52309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d602, d52309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4097 q = 0) : d67373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4097, d67373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4097, d67373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4098 q = 0) : d67374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4098, d67374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4098, d67374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4099 q = 0) : d67375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4099, d67375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4099, d67375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d611 q = 0) : d52318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d611, d52318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro289 q selected
    | true =>
      simp only [d611, d52318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro290 q selected
  have h15 (q : Pattern) (selected : d612 q = 0) : d52319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, d52319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d612, d52319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d613 q = 0) : d52320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d52320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d613, d52320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d614 q = 0) : d52321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, d52321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d614, d52321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d617 q = 0) : d52324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, d52324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro291 q selected
    | true =>
      simp only [d617, d52324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro292 q selected
  have h19 (q : Pattern) (selected : d618 q = 0) : d52325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d52325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d618, d52325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d619 q = 0) : d52326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d52326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d619, d52326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d621 q = 0) : d52328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro293 q selected
    | true =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
  have h22 (q : Pattern) (selected : d624 q = 0) : d52249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d624, d52249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro294 q selected
    | true =>
      simp only [d624, d52249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro295 q selected
  have h23 (q : Pattern) (selected : d625 q = 0) : d52329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d625, d52329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d625, d52329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d4101 q = 0) : d67377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4101, d67377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d4101, d67377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d4102 q = 0) : d67378 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4102, d67378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4102, d67378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d4103 q = 0) : d67379 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4103, d67379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4103, d67379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d4104 q = 0) : d67380 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4104, d67380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4104, d67380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro2598 (p : Pattern) (selected : d4111 p = 0) : d67387 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d621 q = 0) : d52328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro293 q selected
    | true =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
  have h2 (q : Pattern) (selected : d624 q = 0) : d52249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d624, d52249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro294 q selected
    | true =>
      simp only [d624, d52249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro295 q selected
  have h3 (q : Pattern) (selected : d625 q = 0) : d52329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d625, d52329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d625, d52329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4101 q = 0) : d67377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4101, d67377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4101, d67377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4109 q = 0) : d67385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4109, d67385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4109, d67385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4110 q = 0) : d67386 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4110, d67386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4110, d67386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4111 q = 0) : d67387 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4111, d67387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4111, d67387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2599 (p : Pattern) (selected : d4120 p = 0) : d67396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d690 q = 0) : d52394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d690, d52394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro304 q selected
    | true =>
      simp only [d690, d52394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro306 q selected
  have h2 (q : Pattern) (selected : d718 q = 0) : d52399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d718, d52399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro310 q selected
    | true =>
      simp only [d718, d52399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro311 q selected
  have h3 (q : Pattern) (selected : d719 q = 0) : d52400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d719, d52400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d719, d52400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4117 q = 0) : d67393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4117, d67393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4117, d67393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4118 q = 0) : d67394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4118, d67394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4118, d67394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4119 q = 0) : d67395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4119, d67395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4119, d67395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4120 q = 0) : d67396 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4120, d67396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4120, d67396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2600 (p : Pattern) (selected : d4126 p = 0) : d67402 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d498 q = 0) : d52245 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro267 q selected
  have h2 (q : Pattern) (selected : d499 q = 0) : d52246 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d508 q = 0) : d52255 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro267 q selected
    | true =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro270 q selected
  have h4 (q : Pattern) (selected : d509 q = 0) : d52256 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d510 q = 0) : d52257 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4105 q = 0) : d67381 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4105, d67381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2596 q selected
    | true =>
      simp only [d4105, d67381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2597 q selected
  have h7 (q : Pattern) (selected : d645 q = 0) : d52349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d52349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro297 q selected
    | true =>
      simp only [d645, d52349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro298 q selected
  have h8 (q : Pattern) (selected : d4106 q = 0) : d67382 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4106, d67382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4106, d67382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4107 q = 0) : d67383 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4107, d67383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4107, d67383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d4108 q = 0) : d67384 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4108, d67384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4108, d67384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4112 q = 0) : d67388 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4112, d67388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4112, d67388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2598 q selected
  have h12 (q : Pattern) (selected : d654 q = 0) : d52358 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro300 q selected
  have h13 (q : Pattern) (selected : d4113 q = 0) : d67389 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4113, d67389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4113, d67389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4114 q = 0) : d67390 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4114, d67390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4114, d67390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4115 q = 0) : d67391 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4115, d67391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d4115, d67391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d4116 q = 0) : d67392 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4116, d67392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4116, d67392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4121 q = 0) : d67397 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4121, d67397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4121, d67397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2599 q selected
  have h18 (q : Pattern) (selected : d737 q = 0) : d52414 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro314 q selected
  have h19 (q : Pattern) (selected : d4122 q = 0) : d67398 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4122, d67398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4122, d67398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d4123 q = 0) : d67399 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4123, d67399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d4123, d67399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d4124 q = 0) : d67400 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4124, d67400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4124, d67400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d4125 q = 0) : d67401 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4125, d67401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d4125, d67401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d4126 q = 0) : d67402 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4126, d67402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4126, d67402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro2601 (p : Pattern) (selected : d4132 p = 0) : d67408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4127 q = 0) : d67403 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4127, d67403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4127, d67403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2600 q selected
  have h2 (q : Pattern) (selected : d4128 q = 0) : d67404 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4128, d67404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4128, d67404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4129 q = 0) : d67405 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4129, d67405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4129, d67405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4130 q = 0) : d67406 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4130, d67406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4130, d67406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4131 q = 0) : d67407 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4131, d67407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4131, d67407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4132 q = 0) : d67408 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4132, d67408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4132, d67408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2602 (p : Pattern) (selected : d4137 p = 0) : d67413 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d807 q = 0) : d52484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro329 q selected
    | true =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro330 q selected
  have h2 (q : Pattern) (selected : d808 q = 0) : d52485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d809 q = 0) : d52486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d810 q = 0) : d52487 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d52487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d810, d52487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d817 q = 0) : d52494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro331 q selected
    | true =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro332 q selected
  have h6 (q : Pattern) (selected : d818 q = 0) : d52495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d819 q = 0) : d52496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d852 q = 0) : d52529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro338 q selected
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
  have h9 (q : Pattern) (selected : d907 q = 0) : d52461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro348 q selected
    | true =>
      simp only [d907, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro349 q selected
  have h10 (q : Pattern) (selected : d908 q = 0) : d52530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d52530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d908, d52530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4134 q = 0) : d67410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4134, d67410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4134, d67410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4135 q = 0) : d67411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4135, d67411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4135, d67411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4136 q = 0) : d67412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4136, d67412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4136, d67412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4137 q = 0) : d67413 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4137, d67413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4137, d67413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro2603 (p : Pattern) (selected : d4141 p = 0) : d67417 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d807 q = 0) : d52484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro329 q selected
    | true =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro330 q selected
  have h2 (q : Pattern) (selected : d808 q = 0) : d52485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d809 q = 0) : d52486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d810 q = 0) : d52487 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d52487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d810, d52487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d817 q = 0) : d52494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro331 q selected
    | true =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro332 q selected
  have h6 (q : Pattern) (selected : d818 q = 0) : d52495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d819 q = 0) : d52496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d852 q = 0) : d52529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro338 q selected
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
  have h9 (q : Pattern) (selected : d907 q = 0) : d52461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro348 q selected
    | true =>
      simp only [d907, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro349 q selected
  have h10 (q : Pattern) (selected : d908 q = 0) : d52530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d52530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d908, d52530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4134 q = 0) : d67410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4134, d67410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4134, d67410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4135 q = 0) : d67411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4135, d67411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4135, d67411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4136 q = 0) : d67412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4136, d67412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4136, d67412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d917 q = 0) : d52539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, d52539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro351 q selected
    | true =>
      simp only [d917, d52539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro352 q selected
  have h15 (q : Pattern) (selected : d918 q = 0) : d52540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d52540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d918, d52540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d919 q = 0) : d52541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d52541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d919, d52541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d920 q = 0) : d52542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, d52542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d920, d52542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d923 q = 0) : d52545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, d52545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro353 q selected
    | true =>
      simp only [d923, d52545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro354 q selected
  have h19 (q : Pattern) (selected : d924 q = 0) : d52546 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d52546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d924, d52546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d925 q = 0) : d52547 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d52547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d925, d52547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d927 q = 0) : d52549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro355 q selected
    | true =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
  have h22 (q : Pattern) (selected : d930 q = 0) : d52471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d930, d52471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro356 q selected
    | true =>
      simp only [d930, d52471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro357 q selected
  have h23 (q : Pattern) (selected : d931 q = 0) : d52550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d931, d52550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d931, d52550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d4138 q = 0) : d67414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4138, d67414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d4138, d67414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d4139 q = 0) : d67415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4139, d67415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4139, d67415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d4140 q = 0) : d67416 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4140, d67416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4140, d67416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d4141 q = 0) : d67417 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4141, d67417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4141, d67417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro2604 (p : Pattern) (selected : d4148 p = 0) : d67424 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d927 q = 0) : d52549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro355 q selected
    | true =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
  have h2 (q : Pattern) (selected : d930 q = 0) : d52471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d930, d52471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro356 q selected
    | true =>
      simp only [d930, d52471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro357 q selected
  have h3 (q : Pattern) (selected : d931 q = 0) : d52550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d931, d52550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d931, d52550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4138 q = 0) : d67414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4138, d67414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4138, d67414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4146 q = 0) : d67422 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4146, d67422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4146, d67422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4147 q = 0) : d67423 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4147, d67423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4147, d67423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4148 q = 0) : d67424 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4148, d67424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4148, d67424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2605 (p : Pattern) (selected : d4157 p = 0) : d67433 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1012 q = 0) : d52631 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1012, d52631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro369 q selected
    | true =>
      simp only [d1012, d52631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro371 q selected
  have h2 (q : Pattern) (selected : d1051 q = 0) : d52636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1051, d52636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro377 q selected
    | true =>
      simp only [d1051, d52636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro378 q selected
  have h3 (q : Pattern) (selected : d1052 q = 0) : d52637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1052, d52637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1052, d52637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4154 q = 0) : d67430 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4154, d67430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4154, d67430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4155 q = 0) : d67431 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4155, d67431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4155, d67431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4156 q = 0) : d67432 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4156, d67432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4156, d67432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4157 q = 0) : d67433 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4157, d67433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4157, d67433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2606 (p : Pattern) (selected : d4163 p = 0) : d67439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d790 q = 0) : d52467 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro325 q selected
  have h2 (q : Pattern) (selected : d791 q = 0) : d52468 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d800 q = 0) : d52477 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro325 q selected
    | true =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro328 q selected
  have h4 (q : Pattern) (selected : d801 q = 0) : d52478 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d802 q = 0) : d52479 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4142 q = 0) : d67418 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4142, d67418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2602 q selected
    | true =>
      simp only [d4142, d67418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2603 q selected
  have h7 (q : Pattern) (selected : d951 q = 0) : d52570 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro359 q selected
    | true =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro360 q selected
  have h8 (q : Pattern) (selected : d4143 q = 0) : d67419 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4143, d67419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4143, d67419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4144 q = 0) : d67420 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4144, d67420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4144, d67420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d4145 q = 0) : d67421 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4145, d67421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4145, d67421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4149 q = 0) : d67425 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4149, d67425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4149, d67425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2604 q selected
  have h12 (q : Pattern) (selected : d960 q = 0) : d52579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro362 q selected
  have h13 (q : Pattern) (selected : d4150 q = 0) : d67426 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4150, d67426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4150, d67426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4151 q = 0) : d67427 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4151, d67427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4151, d67427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4152 q = 0) : d67428 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4152, d67428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d4152, d67428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d4153 q = 0) : d67429 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4153, d67429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4153, d67429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4158 q = 0) : d67434 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4158, d67434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4158, d67434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2605 q selected
  have h18 (q : Pattern) (selected : d1070 q = 0) : d52651 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro381 q selected
  have h19 (q : Pattern) (selected : d4159 q = 0) : d67435 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4159, d67435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4159, d67435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d4160 q = 0) : d67436 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4160, d67436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d4160, d67436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d4161 q = 0) : d67437 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4161, d67437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4161, d67437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d4162 q = 0) : d67438 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4162, d67438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d4162, d67438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d4163 q = 0) : d67439 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4163, d67439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4163, d67439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro2607 (p : Pattern) (selected : d4169 p = 0) : d67445 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4164 q = 0) : d67440 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4164, d67440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4164, d67440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2606 q selected
  have h2 (q : Pattern) (selected : d4165 q = 0) : d67441 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4165, d67441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4165, d67441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4166 q = 0) : d67442 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4166, d67442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4166, d67442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4167 q = 0) : d67443 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4167, d67443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4167, d67443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4168 q = 0) : d67444 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4168, d67444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4168, d67444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4169 q = 0) : d67445 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4169, d67445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4169, d67445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2608 (p : Pattern) (selected : d4175 p = 0) : d67451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1186 q = 0) : d52767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro401 q selected
    | true =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro402 q selected
  have h2 (q : Pattern) (selected : d1187 q = 0) : d52768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1188 q = 0) : d52769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1189 q = 0) : d52770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1196 q = 0) : d52777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro403 q selected
    | true =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro404 q selected
  have h6 (q : Pattern) (selected : d1197 q = 0) : d52778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1198 q = 0) : d52779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1228 q = 0) : d52809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro410 q selected
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
  have h9 (q : Pattern) (selected : d1318 q = 0) : d52744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro424 q selected
    | true =>
      simp only [d1318, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro425 q selected
  have h10 (q : Pattern) (selected : d1319 q = 0) : d52810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d52810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1319, d52810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4172 q = 0) : d67448 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4172, d67448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4172, d67448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4173 q = 0) : d67449 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4173, d67449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4173, d67449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4174 q = 0) : d67450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4174, d67450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4174, d67450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4175 q = 0) : d67451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4175, d67451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4175, d67451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro2609 (p : Pattern) (selected : d4179 p = 0) : d67455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1186 q = 0) : d52767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro401 q selected
    | true =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro402 q selected
  have h2 (q : Pattern) (selected : d1187 q = 0) : d52768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1188 q = 0) : d52769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1189 q = 0) : d52770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1196 q = 0) : d52777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro403 q selected
    | true =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro404 q selected
  have h6 (q : Pattern) (selected : d1197 q = 0) : d52778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1198 q = 0) : d52779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1228 q = 0) : d52809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro410 q selected
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
  have h9 (q : Pattern) (selected : d1318 q = 0) : d52744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro424 q selected
    | true =>
      simp only [d1318, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro425 q selected
  have h10 (q : Pattern) (selected : d1319 q = 0) : d52810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d52810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1319, d52810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4172 q = 0) : d67448 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4172, d67448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4172, d67448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4173 q = 0) : d67449 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4173, d67449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4173, d67449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4174 q = 0) : d67450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4174, d67450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4174, d67450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1328 q = 0) : d52819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d52819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro427 q selected
    | true =>
      simp only [d1328, d52819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro428 q selected
  have h15 (q : Pattern) (selected : d1329 q = 0) : d52820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d52820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1329, d52820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d1330 q = 0) : d52821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d52821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d1330, d52821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d1331 q = 0) : d52822 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d52822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1331, d52822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d1334 q = 0) : d52825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d52825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro429 q selected
    | true =>
      simp only [d1334, d52825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro430 q selected
  have h19 (q : Pattern) (selected : d1335 q = 0) : d52826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d52826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1335, d52826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d1336 q = 0) : d52827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d52827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d1336, d52827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d1338 q = 0) : d52829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro431 q selected
    | true =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
  have h22 (q : Pattern) (selected : d1341 q = 0) : d52754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1341, d52754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro432 q selected
    | true =>
      simp only [d1341, d52754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro433 q selected
  have h23 (q : Pattern) (selected : d1342 q = 0) : d52830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1342, d52830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d1342, d52830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d4176 q = 0) : d67452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4176, d67452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d4176, d67452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d4177 q = 0) : d67453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4177, d67453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4177, d67453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d4178 q = 0) : d67454 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4178, d67454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4178, d67454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d4179 q = 0) : d67455 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4179, d67455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4179, d67455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro2610 (p : Pattern) (selected : d4186 p = 0) : d67462 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1338 q = 0) : d52829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro431 q selected
    | true =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
  have h2 (q : Pattern) (selected : d1341 q = 0) : d52754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1341, d52754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro432 q selected
    | true =>
      simp only [d1341, d52754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro433 q selected
  have h3 (q : Pattern) (selected : d1342 q = 0) : d52830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1342, d52830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1342, d52830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4176 q = 0) : d67452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4176, d67452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4176, d67452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4184 q = 0) : d67460 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4184, d67460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4184, d67460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4185 q = 0) : d67461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4185, d67461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4185, d67461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4186 q = 0) : d67462 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4186, d67462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4186, d67462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2611 (p : Pattern) (selected : d4195 p = 0) : d67471 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1437 q = 0) : d52925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1437, d52925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro445 q selected
    | true =>
      simp only [d1437, d52925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro447 q selected
  have h2 (q : Pattern) (selected : d1485 q = 0) : d52930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1485, d52930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro453 q selected
    | true =>
      simp only [d1485, d52930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro454 q selected
  have h3 (q : Pattern) (selected : d1486 q = 0) : d52931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1486, d52931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1486, d52931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4192 q = 0) : d67468 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4192, d67468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4192, d67468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4193 q = 0) : d67469 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4193, d67469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4193, d67469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4194 q = 0) : d67470 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4194, d67470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4194, d67470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4195 q = 0) : d67471 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4195, d67471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4195, d67471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2612 (p : Pattern) (selected : d4201 p = 0) : d67477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1169 q = 0) : d52750 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro397 q selected
  have h2 (q : Pattern) (selected : d1170 q = 0) : d52751 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1179 q = 0) : d52760 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro397 q selected
    | true =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro400 q selected
  have h4 (q : Pattern) (selected : d1180 q = 0) : d52761 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1181 q = 0) : d52762 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4180 q = 0) : d67456 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4180, d67456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2608 q selected
    | true =>
      simp only [d4180, d67456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2609 q selected
  have h7 (q : Pattern) (selected : d1362 q = 0) : d52850 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro435 q selected
    | true =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro436 q selected
  have h8 (q : Pattern) (selected : d4181 q = 0) : d67457 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4181, d67457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4181, d67457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4182 q = 0) : d67458 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4182, d67458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4182, d67458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d4183 q = 0) : d67459 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4183, d67459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4183, d67459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4187 q = 0) : d67463 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4187, d67463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4187, d67463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2610 q selected
  have h12 (q : Pattern) (selected : d1371 q = 0) : d52859 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro438 q selected
  have h13 (q : Pattern) (selected : d4188 q = 0) : d67464 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4188, d67464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4188, d67464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4189 q = 0) : d67465 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4189, d67465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4189, d67465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4190 q = 0) : d67466 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4190, d67466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d4190, d67466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d4191 q = 0) : d67467 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4191, d67467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4191, d67467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4196 q = 0) : d67472 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4196, d67472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4196, d67472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2611 q selected
  have h18 (q : Pattern) (selected : d1504 q = 0) : d52945 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro457 q selected
  have h19 (q : Pattern) (selected : d4197 q = 0) : d67473 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4197, d67473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4197, d67473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d4198 q = 0) : d67474 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4198, d67474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d4198, d67474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d4199 q = 0) : d67475 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4199, d67475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4199, d67475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d4200 q = 0) : d67476 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4200, d67476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d4200, d67476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d4201 q = 0) : d67477 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4201, d67477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4201, d67477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro2613 (p : Pattern) (selected : d4207 p = 0) : d67483 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4202 q = 0) : d67478 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4202, d67478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4202, d67478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2612 q selected
  have h2 (q : Pattern) (selected : d4203 q = 0) : d67479 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4203, d67479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4203, d67479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4204 q = 0) : d67480 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4204, d67480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4204, d67480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4205 q = 0) : d67481 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4205, d67481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4205, d67481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4206 q = 0) : d67482 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4206, d67482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4206, d67482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4207 q = 0) : d67483 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4207, d67483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4207, d67483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2614 (p : Pattern) (selected : d4214 p = 0) : d67490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1647 q = 0) : d53088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro483 q selected
    | true =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro484 q selected
  have h2 (q : Pattern) (selected : d1648 q = 0) : d53089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1649 q = 0) : d53090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1650 q = 0) : d53091 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1657 q = 0) : d53098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro485 q selected
    | true =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro486 q selected
  have h6 (q : Pattern) (selected : d1658 q = 0) : d53099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1659 q = 0) : d53100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1683 q = 0) : d53124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro490 q selected
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
  have h9 (q : Pattern) (selected : d1795 q = 0) : d53065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro510 q selected
    | true =>
      simp only [d1795, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro511 q selected
  have h10 (q : Pattern) (selected : d1796 q = 0) : d53125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d53125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1796, d53125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4211 q = 0) : d67487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4211, d67487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4211, d67487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4212 q = 0) : d67488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4212, d67488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4212, d67488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4213 q = 0) : d67489 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4213, d67489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4213, d67489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4214 q = 0) : d67490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4214, d67490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4214, d67490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro2615 (p : Pattern) (selected : d4218 p = 0) : d67494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1647 q = 0) : d53088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro483 q selected
    | true =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro484 q selected
  have h2 (q : Pattern) (selected : d1648 q = 0) : d53089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1649 q = 0) : d53090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1650 q = 0) : d53091 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1657 q = 0) : d53098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro485 q selected
    | true =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro486 q selected
  have h6 (q : Pattern) (selected : d1658 q = 0) : d53099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1659 q = 0) : d53100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1683 q = 0) : d53124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro490 q selected
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
  have h9 (q : Pattern) (selected : d1795 q = 0) : d53065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro510 q selected
    | true =>
      simp only [d1795, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro511 q selected
  have h10 (q : Pattern) (selected : d1796 q = 0) : d53125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d53125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1796, d53125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4211 q = 0) : d67487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4211, d67487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4211, d67487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4212 q = 0) : d67488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4212, d67488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4212, d67488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4213 q = 0) : d67489 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4213, d67489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4213, d67489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1805 q = 0) : d53134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d53134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro513 q selected
    | true =>
      simp only [d1805, d53134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro514 q selected
  have h15 (q : Pattern) (selected : d1806 q = 0) : d53135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d53135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1806, d53135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d1807 q = 0) : d53136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d53136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d1807, d53136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d1808 q = 0) : d53137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d53137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1808, d53137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d1811 q = 0) : d53140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d53140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro515 q selected
    | true =>
      simp only [d1811, d53140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro516 q selected
  have h19 (q : Pattern) (selected : d1812 q = 0) : d53141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d53141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1812, d53141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d1813 q = 0) : d53142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d53142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d1813, d53142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d1815 q = 0) : d53144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro517 q selected
    | true =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
  have h22 (q : Pattern) (selected : d1818 q = 0) : d53075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1818, d53075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro518 q selected
    | true =>
      simp only [d1818, d53075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro519 q selected
  have h23 (q : Pattern) (selected : d1819 q = 0) : d53145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1819, d53145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d1819, d53145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d4215 q = 0) : d67491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4215, d67491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d4215, d67491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d4216 q = 0) : d67492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4216, d67492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4216, d67492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d4217 q = 0) : d67493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4217, d67493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4217, d67493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d4218 q = 0) : d67494 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4218, d67494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4218, d67494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro2616 (p : Pattern) (selected : d4225 p = 0) : d67501 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1815 q = 0) : d53144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro517 q selected
    | true =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
  have h2 (q : Pattern) (selected : d1818 q = 0) : d53075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1818, d53075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro518 q selected
    | true =>
      simp only [d1818, d53075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro519 q selected
  have h3 (q : Pattern) (selected : d1819 q = 0) : d53145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1819, d53145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1819, d53145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4215 q = 0) : d67491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4215, d67491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4215, d67491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4223 q = 0) : d67499 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4223, d67499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4223, d67499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4224 q = 0) : d67500 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4224, d67500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4224, d67500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4225 q = 0) : d67501 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4225, d67501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4225, d67501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2617 (p : Pattern) (selected : d4234 p = 0) : d67510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1914 q = 0) : d53240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1914, d53240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro531 q selected
    | true =>
      simp only [d1914, d53240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro533 q selected
  have h2 (q : Pattern) (selected : d1962 q = 0) : d53245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1962, d53245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro539 q selected
    | true =>
      simp only [d1962, d53245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro540 q selected
  have h3 (q : Pattern) (selected : d1963 q = 0) : d53246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1963, d53246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1963, d53246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4231 q = 0) : d67507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4231, d67507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4231, d67507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4232 q = 0) : d67508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4232, d67508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4232, d67508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4233 q = 0) : d67509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4233, d67509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4233, d67509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4234 q = 0) : d67510 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4234, d67510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4234, d67510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2618 (p : Pattern) (selected : d4240 p = 0) : d67516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1630 q = 0) : d53071 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro479 q selected
  have h2 (q : Pattern) (selected : d1631 q = 0) : d53072 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1640 q = 0) : d53081 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro479 q selected
    | true =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro482 q selected
  have h4 (q : Pattern) (selected : d1641 q = 0) : d53082 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1642 q = 0) : d53083 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4219 q = 0) : d67495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4219, d67495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2614 q selected
    | true =>
      simp only [d4219, d67495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2615 q selected
  have h7 (q : Pattern) (selected : d1839 q = 0) : d53165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro521 q selected
    | true =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro522 q selected
  have h8 (q : Pattern) (selected : d4220 q = 0) : d67496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4220, d67496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4220, d67496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4221 q = 0) : d67497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4221, d67497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4221, d67497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d4222 q = 0) : d67498 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4222, d67498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4222, d67498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4226 q = 0) : d67502 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4226, d67502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4226, d67502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2616 q selected
  have h12 (q : Pattern) (selected : d1848 q = 0) : d53174 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro524 q selected
  have h13 (q : Pattern) (selected : d4227 q = 0) : d67503 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4227, d67503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4227, d67503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4228 q = 0) : d67504 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4228, d67504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4228, d67504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4229 q = 0) : d67505 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4229, d67505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d4229, d67505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d4230 q = 0) : d67506 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4230, d67506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4230, d67506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4235 q = 0) : d67511 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4235, d67511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4235, d67511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2617 q selected
  have h18 (q : Pattern) (selected : d1981 q = 0) : d53260 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro543 q selected
  have h19 (q : Pattern) (selected : d4236 q = 0) : d67512 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4236, d67512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4236, d67512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d4237 q = 0) : d67513 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4237, d67513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d4237, d67513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d4238 q = 0) : d67514 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4238, d67514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4238, d67514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d4239 q = 0) : d67515 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4239, d67515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d4239, d67515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d4240 q = 0) : d67516 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4240, d67516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4240, d67516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro2619 (p : Pattern) (selected : d4246 p = 0) : d67522 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4241 q = 0) : d67517 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4241, d67517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4241, d67517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2618 q selected
  have h2 (q : Pattern) (selected : d4242 q = 0) : d67518 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4242, d67518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4242, d67518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4243 q = 0) : d67519 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4243, d67519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4243, d67519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4244 q = 0) : d67520 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4244, d67520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4244, d67520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4245 q = 0) : d67521 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4245, d67521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4245, d67521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4246 q = 0) : d67522 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4246, d67522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4246, d67522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2620 (p : Pattern) (selected : d4254 p = 0) : d67530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2130 q = 0) : d53409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro572 q selected
    | true =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro573 q selected
  have h2 (q : Pattern) (selected : d2131 q = 0) : d53410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2132 q = 0) : d53411 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2133 q = 0) : d53412 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2140 q = 0) : d53419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro574 q selected
    | true =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro575 q selected
  have h6 (q : Pattern) (selected : d2141 q = 0) : d53420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2142 q = 0) : d53421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2162 q = 0) : d53441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro579 q selected
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
  have h9 (q : Pattern) (selected : d2273 q = 0) : d53386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro600 q selected
    | true =>
      simp only [d2273, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro601 q selected
  have h10 (q : Pattern) (selected : d2274 q = 0) : d53442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d53442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2274, d53442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4251 q = 0) : d67527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4251, d67527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4251, d67527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4252 q = 0) : d67528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4252, d67528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4252, d67528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4253 q = 0) : d67529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4253, d67529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4253, d67529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4254 q = 0) : d67530 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4254, d67530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4254, d67530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro2621 (p : Pattern) (selected : d4258 p = 0) : d67534 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2130 q = 0) : d53409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro572 q selected
    | true =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro573 q selected
  have h2 (q : Pattern) (selected : d2131 q = 0) : d53410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2132 q = 0) : d53411 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2133 q = 0) : d53412 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2140 q = 0) : d53419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro574 q selected
    | true =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro575 q selected
  have h6 (q : Pattern) (selected : d2141 q = 0) : d53420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2142 q = 0) : d53421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2162 q = 0) : d53441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro579 q selected
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
  have h9 (q : Pattern) (selected : d2273 q = 0) : d53386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro600 q selected
    | true =>
      simp only [d2273, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro601 q selected
  have h10 (q : Pattern) (selected : d2274 q = 0) : d53442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d53442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2274, d53442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4251 q = 0) : d67527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4251, d67527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4251, d67527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4252 q = 0) : d67528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4252, d67528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4252, d67528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4253 q = 0) : d67529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4253, d67529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4253, d67529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d2283 q = 0) : d53451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, d53451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro603 q selected
    | true =>
      simp only [d2283, d53451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro604 q selected
  have h15 (q : Pattern) (selected : d2284 q = 0) : d53452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d53452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2284, d53452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d2285 q = 0) : d53453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d53453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d2285, d53453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d2286 q = 0) : d53454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d53454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2286, d53454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d2289 q = 0) : d53457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d53457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro605 q selected
    | true =>
      simp only [d2289, d53457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro606 q selected
  have h19 (q : Pattern) (selected : d2290 q = 0) : d53458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d53458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2290, d53458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d2291 q = 0) : d53459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d53459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d2291, d53459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d2293 q = 0) : d53461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro607 q selected
    | true =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
  have h22 (q : Pattern) (selected : d2296 q = 0) : d53396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2296, d53396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro608 q selected
    | true =>
      simp only [d2296, d53396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro609 q selected
  have h23 (q : Pattern) (selected : d2297 q = 0) : d53462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2297, d53462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d2297, d53462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d4255 q = 0) : d67531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4255, d67531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d4255, d67531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d4256 q = 0) : d67532 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4256, d67532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4256, d67532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d4257 q = 0) : d67533 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4257, d67533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4257, d67533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d4258 q = 0) : d67534 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4258, d67534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4258, d67534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro2622 (p : Pattern) (selected : d4265 p = 0) : d67541 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2293 q = 0) : d53461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro607 q selected
    | true =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
  have h2 (q : Pattern) (selected : d2296 q = 0) : d53396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2296, d53396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro608 q selected
    | true =>
      simp only [d2296, d53396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro609 q selected
  have h3 (q : Pattern) (selected : d2297 q = 0) : d53462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2297, d53462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2297, d53462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4255 q = 0) : d67531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4255, d67531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4255, d67531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4263 q = 0) : d67539 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4263, d67539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4263, d67539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4264 q = 0) : d67540 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4264, d67540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4264, d67540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4265 q = 0) : d67541 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4265, d67541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4265, d67541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2623 (p : Pattern) (selected : d4274 p = 0) : d67550 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2392 q = 0) : d53557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2392, d53557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro621 q selected
    | true =>
      simp only [d2392, d53557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro623 q selected
  have h2 (q : Pattern) (selected : d2440 q = 0) : d53562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2440, d53562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro629 q selected
    | true =>
      simp only [d2440, d53562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro630 q selected
  have h3 (q : Pattern) (selected : d2441 q = 0) : d53563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2441, d53563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2441, d53563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4271 q = 0) : d67547 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4271, d67547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4271, d67547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4272 q = 0) : d67548 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4272, d67548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4272, d67548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4273 q = 0) : d67549 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4273, d67549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4273, d67549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4274 q = 0) : d67550 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4274, d67550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4274, d67550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2624 (p : Pattern) (selected : d4280 p = 0) : d67556 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2113 q = 0) : d53392 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro568 q selected
  have h2 (q : Pattern) (selected : d2114 q = 0) : d53393 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2123 q = 0) : d53402 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro568 q selected
    | true =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro571 q selected
  have h4 (q : Pattern) (selected : d2124 q = 0) : d53403 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2125 q = 0) : d53404 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4259 q = 0) : d67535 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4259, d67535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2620 q selected
    | true =>
      simp only [d4259, d67535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2621 q selected
  have h7 (q : Pattern) (selected : d2317 q = 0) : d53482 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro611 q selected
    | true =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro612 q selected
  have h8 (q : Pattern) (selected : d4260 q = 0) : d67536 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4260, d67536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4260, d67536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4261 q = 0) : d67537 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4261, d67537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4261, d67537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d4262 q = 0) : d67538 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4262, d67538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4262, d67538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4266 q = 0) : d67542 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4266, d67542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4266, d67542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2622 q selected
  have h12 (q : Pattern) (selected : d2326 q = 0) : d53491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro614 q selected
  have h13 (q : Pattern) (selected : d4267 q = 0) : d67543 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4267, d67543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4267, d67543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4268 q = 0) : d67544 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4268, d67544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4268, d67544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4269 q = 0) : d67545 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4269, d67545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d4269, d67545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d4270 q = 0) : d67546 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4270, d67546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4270, d67546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4275 q = 0) : d67551 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4275, d67551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4275, d67551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2623 q selected
  have h18 (q : Pattern) (selected : d2459 q = 0) : d53577 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro633 q selected
  have h19 (q : Pattern) (selected : d4276 q = 0) : d67552 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4276, d67552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4276, d67552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d4277 q = 0) : d67553 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4277, d67553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d4277, d67553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d4278 q = 0) : d67554 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4278, d67554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d4278, d67554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d4279 q = 0) : d67555 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4279, d67555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d4279, d67555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d4280 q = 0) : d67556 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4280, d67556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4280, d67556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro2625 (p : Pattern) (selected : d4286 p = 0) : d67562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4281 q = 0) : d67557 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4281, d67557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4281, d67557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2624 q selected
  have h2 (q : Pattern) (selected : d4282 q = 0) : d67558 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4282, d67558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4282, d67558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4283 q = 0) : d67559 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4283, d67559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4283, d67559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4284 q = 0) : d67560 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4284, d67560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4284, d67560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4285 q = 0) : d67561 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4285, d67561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4285, d67561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4286 q = 0) : d67562 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4286, d67562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4286, d67562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2626 (p : Pattern) (selected : d4292 p = 0) : d67568 p = 1 := by
  have h0 (q : Pattern) (selected : d4133 q = 0) : d67409 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4133, d67409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2595 q selected
    | true =>
      simp only [d4133, d67409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2601 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d4170 q = 0) : d67446 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4170, d67446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4170, d67446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2607 q selected
  have h3 (q : Pattern) (selected : d4171 q = 0) : d67447 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4171, d67447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4171, d67447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4208 q = 0) : d67484 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4208, d67484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4208, d67484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2613 q selected
  have h5 (q : Pattern) (selected : d4209 q = 0) : d67485 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4209, d67485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4209, d67485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4210 q = 0) : d67486 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4210, d67486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4210, d67486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4247 q = 0) : d67523 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4247, d67523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4247, d67523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2619 q selected
  have h8 (q : Pattern) (selected : d4248 q = 0) : d67524 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4248, d67524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4248, d67524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4249 q = 0) : d67525 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4249, d67525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4249, d67525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4250 q = 0) : d67526 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4250, d67526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4250, d67526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4287 q = 0) : d67563 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4287, d67563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4287, d67563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2625 q selected
  have h12 (q : Pattern) (selected : d4288 q = 0) : d67564 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4288, d67564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4288, d67564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4289 q = 0) : d67565 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4289, d67565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4289, d67565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4290 q = 0) : d67566 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4290, d67566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4290, d67566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d4291 q = 0) : d67567 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d4291, d67567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4291, d67567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4292 q = 0) : d67568 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d4292, d67568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d4292, d67568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2627 (p : Pattern) (selected : d4298 p = 0) : d67574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4293 q = 0) : d67569 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d4293, d67569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2626 q selected
    | true =>
      simp only [d4293, d67569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4294 q = 0) : d67570 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d4294, d67570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4294, d67570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4295 q = 0) : d67571 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d4295, d67571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4295, d67571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4296 q = 0) : d67572 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d4296, d67572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4296, d67572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4297 q = 0) : d67573 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d4297, d67573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4297, d67573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4298 q = 0) : d67574 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d4298, d67574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4298, d67574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2628 (p : Pattern) (selected : d4304 p = 0) : d67580 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4299 q = 0) : d67575 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d4299, d67575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2627 q selected
    | true =>
      simp only [d4299, d67575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4300 q = 0) : d67576 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d4300, d67576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4300, d67576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4301 q = 0) : d67577 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d4301, d67577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4301, d67577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4302 q = 0) : d67578 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d4302, d67578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4302, d67578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4303 q = 0) : d67579 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d4303, d67579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4303, d67579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4304 q = 0) : d67580 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d4304, d67580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4304, d67580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2629 (p : Pattern) (selected : d4310 p = 0) : d67586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4305 q = 0) : d67581 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d4305, d67581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2628 q selected
    | true =>
      simp only [d4305, d67581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4306 q = 0) : d67582 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d4306, d67582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4306, d67582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4307 q = 0) : d67583 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d4307, d67583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4307, d67583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4308 q = 0) : d67584 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d4308, d67584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4308, d67584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4309 q = 0) : d67585 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d4309, d67585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4309, d67585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4310 q = 0) : d67586 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d4310, d67586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4310, d67586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2630 (p : Pattern) (selected : d4316 p = 0) : d67592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4311 q = 0) : d67587 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d4311, d67587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2629 q selected
    | true =>
      simp only [d4311, d67587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4312 q = 0) : d67588 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d4312, d67588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4312, d67588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4313 q = 0) : d67589 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d4313, d67589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4313, d67589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4314 q = 0) : d67590 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d4314, d67590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4314, d67590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4315 q = 0) : d67591 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d4315, d67591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4315, d67591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4316 q = 0) : d67592 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d4316, d67592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4316, d67592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2631 (p : Pattern) (selected : d4322 p = 0) : d67598 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4317 q = 0) : d67593 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4317, d67593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2630 q selected
    | true =>
      simp only [d4317, d67593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4318 q = 0) : d67594 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4318, d67594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4318, d67594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4319 q = 0) : d67595 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4319, d67595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4319, d67595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4320 q = 0) : d67596 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4320, d67596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4320, d67596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4321 q = 0) : d67597 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4321, d67597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4321, d67597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4322 q = 0) : d67598 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4322, d67598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4322, d67598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2632 (p : Pattern) (selected : d4328 p = 0) : d67604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4323 q = 0) : d67599 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4323, d67599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2631 q selected
    | true =>
      simp only [d4323, d67599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4324 q = 0) : d67600 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4324, d67600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4324, d67600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4325 q = 0) : d67601 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4325, d67601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4325, d67601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4326 q = 0) : d67602 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4326, d67602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4326, d67602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4327 q = 0) : d67603 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4327, d67603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4327, d67603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4328 q = 0) : d67604 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4328, d67604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4328, d67604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2633 (p : Pattern) (selected : d4334 p = 0) : d67610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4329 q = 0) : d67605 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4329, d67605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2632 q selected
    | true =>
      simp only [d4329, d67605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4330 q = 0) : d67606 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4330, d67606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4330, d67606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4331 q = 0) : d67607 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4331, d67607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4331, d67607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4332 q = 0) : d67608 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4332, d67608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4332, d67608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4333 q = 0) : d67609 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4333, d67609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4333, d67609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4334 q = 0) : d67610 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4334, d67610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4334, d67610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2634 (p : Pattern) (selected : d4029 p = 1) : d67614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d120 q = 1) : d120 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d126 q = 1) : d126 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d157 q = 1) : d157 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
    | true =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189 q = 1) : d4335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4026 q = 1) : d67611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4026, d67611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4026, d67611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4027 q = 1) : d67612 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4027, d67612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4027, d67612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4028 q = 1) : d67613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4028, d67613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4028, d67613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4029 q = 1) : d67614 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4029, d67614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4029, d67614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro2635 (p : Pattern) (selected : d4033 p = 1) : d67618 p = 1 := by
  have h0 (q : Pattern) (selected : d120 q = 1) : d120 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d126 q = 1) : d126 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d157 q = 1) : d157 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
    | true =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189 q = 1) : d4335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4026 q = 1) : d67611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4026, d67611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4026, d67611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d4027 q = 1) : d67612 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4027, d67612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4027, d67612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4028 q = 1) : d67613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4028, d67613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4028, d67613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d198 q = 1) : d198 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d202 q = 1) : d202 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d204 q = 1) : d204 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
    | true =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h13 (q : Pattern) (selected : d207 q = 1) : d4340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207, d4340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d207, d4340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4030 q = 1) : d67615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4030, d67615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4030, d67615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h15 (q : Pattern) (selected : d4031 q = 1) : d67616 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4031, d67616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4031, d67616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4032 q = 1) : d67617 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4032, d67617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4032, d67617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4033 q = 1) : d67618 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4033, d67618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4033, d67618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro2636 (p : Pattern) (selected : d4040 p = 1) : d67625 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d204 q = 1) : d204 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
    | true =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d207 q = 1) : d4340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207, d4340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d207, d4340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4030 q = 1) : d67615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4030, d67615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4030, d67615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4038 q = 1) : d67623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4038, d67623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4038, d67623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4039 q = 1) : d67624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4039, d67624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4039, d67624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4040 q = 1) : d67625 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4040, d67625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4040, d67625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2637 (p : Pattern) (selected : d4049 p = 1) : d67634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d244 q = 1) : d244 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d263 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11 q selected
    | true =>
      simp only [d263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d264 q = 1) : d4355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d264, d4355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d264, d4355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4046 q = 1) : d67631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4046, d67631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4046, d67631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4047 q = 1) : d67632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4047, d67632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4047, d67632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4048 q = 1) : d67633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4048, d67633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4048, d67633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4049 q = 1) : d67634 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4049, d67634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4049, d67634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2638 (p : Pattern) (selected : d4055 p = 1) : d67640 p = 1 := by
  have h0 (q : Pattern) (selected : d114 q = 1) : d114 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4034 q = 1) : d67619 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4034, d67619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2634 q selected
    | true =>
      simp only [d4034, d67619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2635 q selected
  have h2 (q : Pattern) (selected : d214 q = 1) : d214 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d4035 q = 1) : d67620 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4035, d67620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4035, d67620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d4036 q = 1) : d67621 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4036, d67621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4036, d67621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4037 q = 1) : d67622 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4037, d67622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4037, d67622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4041 q = 1) : d67626 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4041, d67626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4041, d67626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2636 q selected
  have h8 (q : Pattern) (selected : d4042 q = 1) : d67627 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4042, d67627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4042, d67627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d4043 q = 1) : d67628 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4043, d67628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4043, d67628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d4044 q = 1) : d67629 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4044, d67629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4044, d67629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d4045 q = 1) : d67630 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4045, d67630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4045, d67630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d4050 q = 1) : d67635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4050, d67635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4050, d67635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2637 q selected
  have h13 (q : Pattern) (selected : d4051 q = 1) : d67636 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4051, d67636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4051, d67636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d4052 q = 1) : d67637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4052, d67637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4052, d67637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d4053 q = 1) : d67638 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4053, d67638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d4053, d67638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d4054 q = 1) : d67639 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4054, d67639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d4054, d67639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d4055 q = 1) : d67640 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4055, d67640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4055, d67640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro2639 (p : Pattern) (selected : d4064 p = 1) : d67649 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300 q = 1) : d300 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d306 q = 1) : d306 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d337 q = 1) : d337 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18 q selected
    | true =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h5 (q : Pattern) (selected : d369 q = 1) : d4371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4061 q = 1) : d67646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4061, d67646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4061, d67646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4062 q = 1) : d67647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4062, d67647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4062, d67647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4063 q = 1) : d67648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4063, d67648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4063, d67648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4064 q = 1) : d67649 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4064, d67649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4064, d67649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro2640 (p : Pattern) (selected : d4068 p = 1) : d67653 p = 1 := by
  have h0 (q : Pattern) (selected : d300 q = 1) : d300 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d306 q = 1) : d306 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d337 q = 1) : d337 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18 q selected
    | true =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h4 (q : Pattern) (selected : d369 q = 1) : d4371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d4061 q = 1) : d67646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4061, d67646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4061, d67646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4062 q = 1) : d67647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4062, d67647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4062, d67647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4063 q = 1) : d67648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4063, d67648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4063, d67648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d380 q = 1) : d380 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d384 q = 1) : d384 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d386 q = 1) : d386 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d388 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20 q selected
    | true =>
      simp only [d388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
  have h13 (q : Pattern) (selected : d389 q = 1) : d4376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d389, d4376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d389, d4376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4065 q = 1) : d67650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4065, d67650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4065, d67650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h15 (q : Pattern) (selected : d4066 q = 1) : d67651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4066, d67651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4066, d67651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4067 q = 1) : d67652 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4067, d67652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4067, d67652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4068 q = 1) : d67653 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4068, d67653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4068, d67653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro2641 (p : Pattern) (selected : d4075 p = 1) : d67660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d386 q = 1) : d386 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d388 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro20 q selected
    | true =>
      simp only [d388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
  have h3 (q : Pattern) (selected : d389 q = 1) : d4376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d389, d4376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d389, d4376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4065 q = 1) : d67650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4065, d67650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4065, d67650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4073 q = 1) : d67658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4073, d67658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4073, d67658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4074 q = 1) : d67659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4074, d67659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4074, d67659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4075 q = 1) : d67660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4075, d67660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4075, d67660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2642 (p : Pattern) (selected : d4084 p = 1) : d67669 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d430 q = 1) : d430 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25 q selected
    | true =>
      simp only [d449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11 q selected
  have h3 (q : Pattern) (selected : d450 q = 1) : d4391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d450, d4391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d450, d4391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4081 q = 1) : d67666 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4081, d67666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4081, d67666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4082 q = 1) : d67667 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4082, d67667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4082, d67667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4083 q = 1) : d67668 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4083, d67668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4083, d67668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4084 q = 1) : d67669 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4084, d67669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4084, d67669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2643 (p : Pattern) (selected : d4090 p = 1) : d67675 p = 1 := by
  have h0 (q : Pattern) (selected : d294 q = 1) : d294 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4069 q = 1) : d67654 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4069, d67654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2639 q selected
    | true =>
      simp only [d4069, d67654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2640 q selected
  have h2 (q : Pattern) (selected : d398 q = 1) : d398 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d4070 q = 1) : d67655 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4070, d67655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4070, d67655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d4071 q = 1) : d67656 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4071, d67656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4071, d67656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4072 q = 1) : d67657 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4072, d67657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4072, d67657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4076 q = 1) : d67661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4076, d67661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4076, d67661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2641 q selected
  have h8 (q : Pattern) (selected : d407 q = 1) : d407 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d4077 q = 1) : d67662 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4077, d67662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4077, d67662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4078 q = 1) : d67663 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4078, d67663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4078, d67663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d4079 q = 1) : d67664 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4079, d67664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4079, d67664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d4080 q = 1) : d67665 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4080, d67665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4080, d67665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4085 q = 1) : d67670 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4085, d67670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4085, d67670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2642 q selected
  have h14 (q : Pattern) (selected : d463 q = 1) : d463 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d4086 q = 1) : d67671 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4086, d67671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4086, d67671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4087 q = 1) : d67672 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4087, d67672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d4087, d67672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d4088 q = 1) : d67673 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4088, d67673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4088, d67673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d4089 q = 1) : d67674 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4089, d67674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4089, d67674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d4090 q = 1) : d67675 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4090, d67675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4090, d67675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro2644 (p : Pattern) (selected : d4096 p = 1) : d67681 p = 1 := by
  have h0 (q : Pattern) (selected : d99 q = 1) : d99 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d4056 q = 1) : d67641 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4056, d67641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4056, d67641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2638 q selected
  have h3 (q : Pattern) (selected : d4057 q = 1) : d67642 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4057, d67642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4057, d67642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4058 q = 1) : d67643 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4058, d67643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4058, d67643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4059 q = 1) : d67644 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4059, d67644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4059, d67644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4060 q = 1) : d67645 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4060, d67645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4060, d67645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4091 q = 1) : d67676 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4091, d67676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4091, d67676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2643 q selected
  have h8 (q : Pattern) (selected : d4092 q = 1) : d67677 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4092, d67677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4092, d67677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4093 q = 1) : d67678 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4093, d67678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4093, d67678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4094 q = 1) : d67679 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4094, d67679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4094, d67679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4095 q = 1) : d67680 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4095, d67680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4095, d67680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d4096 q = 1) : d67681 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4096, d67681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4096, d67681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro2645 (p : Pattern) (selected : d4100 p = 1) : d67685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d518 q = 1) : d518 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d527 q = 1) : d527 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d561 q = 1) : d561 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34 q selected
    | true =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35 q selected
  have h5 (q : Pattern) (selected : d602 q = 1) : d4408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4097 q = 1) : d67682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4097, d67682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4097, d67682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4098 q = 1) : d67683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4098, d67683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4098, d67683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4099 q = 1) : d67684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4099, d67684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4099, d67684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4100 q = 1) : d67685 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4100, d67685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4100, d67685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro2646 (p : Pattern) (selected : d4104 p = 1) : d67689 p = 1 := by
  have h0 (q : Pattern) (selected : d518 q = 1) : d518 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d527 q = 1) : d527 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d561 q = 1) : d561 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34 q selected
    | true =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35 q selected
  have h4 (q : Pattern) (selected : d602 q = 1) : d4408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d4097 q = 1) : d67682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4097, d67682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4097, d67682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4098 q = 1) : d67683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4098, d67683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4098, d67683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4099 q = 1) : d67684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4099, d67684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4099, d67684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d614 q = 1) : d614 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d619 q = 1) : d619 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d621 q = 1) : d621 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d624 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37 q selected
    | true =>
      simp only [d624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38 q selected
  have h13 (q : Pattern) (selected : d625 q = 1) : d4413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d625, d4413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d625, d4413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4101 q = 1) : d67686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4101, d67686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4101, d67686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h15 (q : Pattern) (selected : d4102 q = 1) : d67687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4102, d67687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4102, d67687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4103 q = 1) : d67688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4103, d67688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4103, d67688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4104 q = 1) : d67689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4104, d67689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4104, d67689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro2647 (p : Pattern) (selected : d4111 p = 1) : d67696 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d621 q = 1) : d621 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d624 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37 q selected
    | true =>
      simp only [d624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38 q selected
  have h3 (q : Pattern) (selected : d625 q = 1) : d4413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d625, d4413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d625, d4413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4101 q = 1) : d67686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4101, d67686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4101, d67686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4109 q = 1) : d67694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4109, d67694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4109, d67694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4110 q = 1) : d67695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4110, d67695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4110, d67695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4111 q = 1) : d67696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4111, d67696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4111, d67696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2648 (p : Pattern) (selected : d4120 p = 1) : d67705 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d690 q = 1) : d690 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d718 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro44 q selected
    | true =>
      simp only [d718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro45 q selected
  have h3 (q : Pattern) (selected : d719 q = 1) : d4428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d719, d4428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d719, d4428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4117 q = 1) : d67702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4117, d67702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4117, d67702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4118 q = 1) : d67703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4118, d67703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4118, d67703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4119 q = 1) : d67704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4119, d67704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4119, d67704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4120 q = 1) : d67705 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4120, d67705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4120, d67705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2649 (p : Pattern) (selected : d4126 p = 1) : d67711 p = 1 := by
  have h0 (q : Pattern) (selected : d510 q = 1) : d510 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4105 q = 1) : d67690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4105, d67690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2645 q selected
    | true =>
      simp only [d4105, d67690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2646 q selected
  have h2 (q : Pattern) (selected : d645 q = 1) : d645 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d4106 q = 1) : d67691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4106, d67691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4106, d67691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d4107 q = 1) : d67692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4107, d67692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4107, d67692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4108 q = 1) : d67693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4108, d67693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4108, d67693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4112 q = 1) : d67697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4112, d67697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4112, d67697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2647 q selected
  have h8 (q : Pattern) (selected : d654 q = 1) : d654 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d4113 q = 1) : d67698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4113, d67698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4113, d67698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4114 q = 1) : d67699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4114, d67699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4114, d67699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d4115 q = 1) : d67700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4115, d67700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4115, d67700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d4116 q = 1) : d67701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4116, d67701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4116, d67701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4121 q = 1) : d67706 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4121, d67706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4121, d67706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2648 q selected
  have h14 (q : Pattern) (selected : d737 q = 1) : d737 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d4122 q = 1) : d67707 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4122, d67707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4122, d67707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4123 q = 1) : d67708 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4123, d67708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d4123, d67708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d4124 q = 1) : d67709 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4124, d67709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4124, d67709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d4125 q = 1) : d67710 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4125, d67710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4125, d67710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d4126 q = 1) : d67711 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4126, d67711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4126, d67711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro2650 (p : Pattern) (selected : d4132 p = 1) : d67717 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4127 q = 1) : d67712 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4127, d67712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4127, d67712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2649 q selected
  have h2 (q : Pattern) (selected : d4128 q = 1) : d67713 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4128, d67713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4128, d67713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4129 q = 1) : d67714 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4129, d67714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4129, d67714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4130 q = 1) : d67715 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4130, d67715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4130, d67715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4131 q = 1) : d67716 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4131, d67716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4131, d67716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4132 q = 1) : d67717 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4132, d67717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4132, d67717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2651 (p : Pattern) (selected : d4137 p = 1) : d67722 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d810 q = 1) : d810 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d819 q = 1) : d819 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d852 q = 1) : d852 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro58 q selected
    | true =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro59 q selected
  have h5 (q : Pattern) (selected : d908 q = 1) : d4446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4134 q = 1) : d67719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4134, d67719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4134, d67719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4135 q = 1) : d67720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4135, d67720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4135, d67720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4136 q = 1) : d67721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4136, d67721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4136, d67721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4137 q = 1) : d67722 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4137, d67722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4137, d67722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro2652 (p : Pattern) (selected : d4141 p = 1) : d67726 p = 1 := by
  have h0 (q : Pattern) (selected : d810 q = 1) : d810 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d819 q = 1) : d819 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d852 q = 1) : d852 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro58 q selected
    | true =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro59 q selected
  have h4 (q : Pattern) (selected : d908 q = 1) : d4446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d4134 q = 1) : d67719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4134, d67719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4134, d67719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4135 q = 1) : d67720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4135, d67720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4135, d67720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4136 q = 1) : d67721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4136, d67721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4136, d67721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d920 q = 1) : d920 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d925 q = 1) : d925 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d927 q = 1) : d927 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro61 q selected
    | true =>
      simp only [d930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro62 q selected
  have h13 (q : Pattern) (selected : d931 q = 1) : d4451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d931, d4451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d931, d4451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4138 q = 1) : d67723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4138, d67723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4138, d67723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h15 (q : Pattern) (selected : d4139 q = 1) : d67724 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4139, d67724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4139, d67724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4140 q = 1) : d67725 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4140, d67725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4140, d67725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4141 q = 1) : d67726 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4141, d67726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4141, d67726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro2653 (p : Pattern) (selected : d4148 p = 1) : d67733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d927 q = 1) : d927 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro61 q selected
    | true =>
      simp only [d930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro62 q selected
  have h3 (q : Pattern) (selected : d931 q = 1) : d4451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d931, d4451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d931, d4451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4138 q = 1) : d67723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4138, d67723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4138, d67723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4146 q = 1) : d67731 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4146, d67731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4146, d67731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4147 q = 1) : d67732 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4147, d67732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4147, d67732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4148 q = 1) : d67733 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4148, d67733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4148, d67733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2654 (p : Pattern) (selected : d4157 p = 1) : d67742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1012 q = 1) : d1012 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro70 q selected
    | true =>
      simp only [d1051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro71 q selected
  have h3 (q : Pattern) (selected : d1052 q = 1) : d4466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1052, d4466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1052, d4466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4154 q = 1) : d67739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4154, d67739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4154, d67739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4155 q = 1) : d67740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4155, d67740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4155, d67740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4156 q = 1) : d67741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4156, d67741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4156, d67741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4157 q = 1) : d67742 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4157, d67742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4157, d67742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2655 (p : Pattern) (selected : d4163 p = 1) : d67748 p = 1 := by
  have h0 (q : Pattern) (selected : d802 q = 1) : d802 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4142 q = 1) : d67727 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4142, d67727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2651 q selected
    | true =>
      simp only [d4142, d67727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2652 q selected
  have h2 (q : Pattern) (selected : d951 q = 1) : d951 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d4143 q = 1) : d67728 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4143, d67728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4143, d67728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d4144 q = 1) : d67729 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4144, d67729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4144, d67729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4145 q = 1) : d67730 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4145, d67730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4145, d67730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4149 q = 1) : d67734 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4149, d67734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4149, d67734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2653 q selected
  have h8 (q : Pattern) (selected : d960 q = 1) : d960 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d4150 q = 1) : d67735 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4150, d67735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4150, d67735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4151 q = 1) : d67736 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4151, d67736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4151, d67736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d4152 q = 1) : d67737 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4152, d67737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4152, d67737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d4153 q = 1) : d67738 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4153, d67738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4153, d67738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4158 q = 1) : d67743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4158, d67743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4158, d67743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2654 q selected
  have h14 (q : Pattern) (selected : d1070 q = 1) : d1070 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d4159 q = 1) : d67744 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4159, d67744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4159, d67744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4160 q = 1) : d67745 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4160, d67745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d4160, d67745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d4161 q = 1) : d67746 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4161, d67746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4161, d67746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d4162 q = 1) : d67747 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4162, d67747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4162, d67747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d4163 q = 1) : d67748 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4163, d67748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4163, d67748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro2656 (p : Pattern) (selected : d4169 p = 1) : d67754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4164 q = 1) : d67749 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4164, d67749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4164, d67749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2655 q selected
  have h2 (q : Pattern) (selected : d4165 q = 1) : d67750 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4165, d67750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4165, d67750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4166 q = 1) : d67751 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4166, d67751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4166, d67751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4167 q = 1) : d67752 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4167, d67752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4167, d67752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4168 q = 1) : d67753 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4168, d67753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4168, d67753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4169 q = 1) : d67754 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4169, d67754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4169, d67754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2657 (p : Pattern) (selected : d4175 p = 1) : d67760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1189 q = 1) : d1189 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1198 q = 1) : d1198 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1228 q = 1) : d1228 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d1318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro88 q selected
    | true =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro89 q selected
  have h5 (q : Pattern) (selected : d1319 q = 1) : d4485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4172 q = 1) : d67757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4172, d67757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4172, d67757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4173 q = 1) : d67758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4173, d67758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4173, d67758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4174 q = 1) : d67759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4174, d67759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4174, d67759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4175 q = 1) : d67760 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4175, d67760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4175, d67760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro2658 (p : Pattern) (selected : d4179 p = 1) : d67764 p = 1 := by
  have h0 (q : Pattern) (selected : d1189 q = 1) : d1189 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1198 q = 1) : d1198 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1228 q = 1) : d1228 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro88 q selected
    | true =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro89 q selected
  have h4 (q : Pattern) (selected : d1319 q = 1) : d4485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d4172 q = 1) : d67757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4172, d67757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4172, d67757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4173 q = 1) : d67758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4173, d67758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4173, d67758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4174 q = 1) : d67759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4174, d67759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4174, d67759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1331 q = 1) : d1331 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d1336 q = 1) : d1336 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d1338 q = 1) : d1338 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d1341 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro91 q selected
    | true =>
      simp only [d1341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro92 q selected
  have h13 (q : Pattern) (selected : d1342 q = 1) : d4490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1342, d4490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1342, d4490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4176 q = 1) : d67761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4176, d67761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4176, d67761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h15 (q : Pattern) (selected : d4177 q = 1) : d67762 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4177, d67762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4177, d67762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4178 q = 1) : d67763 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4178, d67763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4178, d67763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4179 q = 1) : d67764 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4179, d67764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4179, d67764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro2659 (p : Pattern) (selected : d4186 p = 1) : d67771 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1338 q = 1) : d1338 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1341 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro91 q selected
    | true =>
      simp only [d1341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro92 q selected
  have h3 (q : Pattern) (selected : d1342 q = 1) : d4490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1342, d4490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1342, d4490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4176 q = 1) : d67761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4176, d67761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4176, d67761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4184 q = 1) : d67769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4184, d67769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4184, d67769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4185 q = 1) : d67770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4185, d67770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4185, d67770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4186 q = 1) : d67771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4186, d67771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4186, d67771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2660 (p : Pattern) (selected : d4195 p = 1) : d67780 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1437 q = 1) : d1437 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro100 q selected
    | true =>
      simp only [d1485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro101 q selected
  have h3 (q : Pattern) (selected : d1486 q = 1) : d4505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1486, d4505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1486, d4505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4192 q = 1) : d67777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4192, d67777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4192, d67777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4193 q = 1) : d67778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4193, d67778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4193, d67778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4194 q = 1) : d67779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4194, d67779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4194, d67779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4195 q = 1) : d67780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4195, d67780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4195, d67780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2661 (p : Pattern) (selected : d4201 p = 1) : d67786 p = 1 := by
  have h0 (q : Pattern) (selected : d1181 q = 1) : d1181 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4180 q = 1) : d67765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4180, d67765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2657 q selected
    | true =>
      simp only [d4180, d67765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2658 q selected
  have h2 (q : Pattern) (selected : d1362 q = 1) : d1362 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d4181 q = 1) : d67766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4181, d67766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4181, d67766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d4182 q = 1) : d67767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4182, d67767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4182, d67767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4183 q = 1) : d67768 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4183, d67768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4183, d67768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4187 q = 1) : d67772 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4187, d67772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4187, d67772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2659 q selected
  have h8 (q : Pattern) (selected : d1371 q = 1) : d1371 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d4188 q = 1) : d67773 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4188, d67773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4188, d67773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4189 q = 1) : d67774 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4189, d67774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4189, d67774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d4190 q = 1) : d67775 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4190, d67775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4190, d67775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d4191 q = 1) : d67776 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4191, d67776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4191, d67776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4196 q = 1) : d67781 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4196, d67781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4196, d67781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2660 q selected
  have h14 (q : Pattern) (selected : d1504 q = 1) : d1504 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d4197 q = 1) : d67782 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4197, d67782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4197, d67782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4198 q = 1) : d67783 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4198, d67783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d4198, d67783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d4199 q = 1) : d67784 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4199, d67784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4199, d67784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d4200 q = 1) : d67785 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4200, d67785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4200, d67785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d4201 q = 1) : d67786 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4201, d67786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4201, d67786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro2662 (p : Pattern) (selected : d4207 p = 1) : d67792 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4202 q = 1) : d67787 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4202, d67787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4202, d67787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2661 q selected
  have h2 (q : Pattern) (selected : d4203 q = 1) : d67788 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4203, d67788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4203, d67788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4204 q = 1) : d67789 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4204, d67789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4204, d67789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4205 q = 1) : d67790 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4205, d67790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4205, d67790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4206 q = 1) : d67791 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4206, d67791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4206, d67791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4207 q = 1) : d67792 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4207, d67792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4207, d67792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2663 (p : Pattern) (selected : d4214 p = 1) : d67799 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1650 q = 1) : d1650 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1659 q = 1) : d1659 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1683 q = 1) : d1683 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d1795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro124 q selected
    | true =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro125 q selected
  have h5 (q : Pattern) (selected : d1796 q = 1) : d4525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4211 q = 1) : d67796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4211, d67796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4211, d67796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4212 q = 1) : d67797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4212, d67797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4212, d67797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4213 q = 1) : d67798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4213, d67798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4213, d67798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4214 q = 1) : d67799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4214, d67799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4214, d67799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro2664 (p : Pattern) (selected : d4218 p = 1) : d67803 p = 1 := by
  have h0 (q : Pattern) (selected : d1650 q = 1) : d1650 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1659 q = 1) : d1659 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1683 q = 1) : d1683 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro124 q selected
    | true =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro125 q selected
  have h4 (q : Pattern) (selected : d1796 q = 1) : d4525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d4211 q = 1) : d67796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4211, d67796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4211, d67796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4212 q = 1) : d67797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4212, d67797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4212, d67797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4213 q = 1) : d67798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4213, d67798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4213, d67798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1808 q = 1) : d1808 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d1813 q = 1) : d1813 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d1815 q = 1) : d1815 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d1818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro127 q selected
    | true =>
      simp only [d1818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro128 q selected
  have h13 (q : Pattern) (selected : d1819 q = 1) : d4530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1819, d4530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1819, d4530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4215 q = 1) : d67800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4215, d67800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4215, d67800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h15 (q : Pattern) (selected : d4216 q = 1) : d67801 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4216, d67801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4216, d67801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4217 q = 1) : d67802 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4217, d67802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4217, d67802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4218 q = 1) : d67803 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4218, d67803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4218, d67803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro2665 (p : Pattern) (selected : d4225 p = 1) : d67810 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1815 q = 1) : d1815 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro127 q selected
    | true =>
      simp only [d1818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro128 q selected
  have h3 (q : Pattern) (selected : d1819 q = 1) : d4530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1819, d4530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1819, d4530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4215 q = 1) : d67800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4215, d67800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4215, d67800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4223 q = 1) : d67808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4223, d67808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4223, d67808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4224 q = 1) : d67809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4224, d67809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4224, d67809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4225 q = 1) : d67810 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4225, d67810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4225, d67810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2666 (p : Pattern) (selected : d4234 p = 1) : d67819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1914 q = 1) : d1914 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1962 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro136 q selected
    | true =>
      simp only [d1962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro137 q selected
  have h3 (q : Pattern) (selected : d1963 q = 1) : d4545 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1963, d4545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1963, d4545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4231 q = 1) : d67816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4231, d67816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4231, d67816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4232 q = 1) : d67817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4232, d67817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4232, d67817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4233 q = 1) : d67818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4233, d67818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4233, d67818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4234 q = 1) : d67819 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4234, d67819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4234, d67819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2667 (p : Pattern) (selected : d4240 p = 1) : d67825 p = 1 := by
  have h0 (q : Pattern) (selected : d1642 q = 1) : d1642 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4219 q = 1) : d67804 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4219, d67804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2663 q selected
    | true =>
      simp only [d4219, d67804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2664 q selected
  have h2 (q : Pattern) (selected : d1839 q = 1) : d1839 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d4220 q = 1) : d67805 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4220, d67805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4220, d67805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d4221 q = 1) : d67806 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4221, d67806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4221, d67806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4222 q = 1) : d67807 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4222, d67807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4222, d67807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4226 q = 1) : d67811 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4226, d67811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4226, d67811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2665 q selected
  have h8 (q : Pattern) (selected : d1848 q = 1) : d1848 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d4227 q = 1) : d67812 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4227, d67812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4227, d67812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4228 q = 1) : d67813 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4228, d67813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4228, d67813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d4229 q = 1) : d67814 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4229, d67814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4229, d67814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d4230 q = 1) : d67815 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4230, d67815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4230, d67815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4235 q = 1) : d67820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4235, d67820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4235, d67820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2666 q selected
  have h14 (q : Pattern) (selected : d1981 q = 1) : d1981 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d4236 q = 1) : d67821 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4236, d67821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4236, d67821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4237 q = 1) : d67822 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4237, d67822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d4237, d67822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d4238 q = 1) : d67823 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4238, d67823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4238, d67823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d4239 q = 1) : d67824 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4239, d67824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4239, d67824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d4240 q = 1) : d67825 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4240, d67825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4240, d67825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro2668 (p : Pattern) (selected : d4246 p = 1) : d67831 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4241 q = 1) : d67826 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4241, d67826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4241, d67826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2667 q selected
  have h2 (q : Pattern) (selected : d4242 q = 1) : d67827 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4242, d67827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4242, d67827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4243 q = 1) : d67828 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4243, d67828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4243, d67828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4244 q = 1) : d67829 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4244, d67829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4244, d67829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4245 q = 1) : d67830 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4245, d67830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4245, d67830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4246 q = 1) : d67831 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4246, d67831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4246, d67831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2669 (p : Pattern) (selected : d4254 p = 1) : d67839 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2133 q = 1) : d2133 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2142 q = 1) : d2142 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d2162 q = 1) : d2162 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d2273 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro161 q selected
    | true =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro162 q selected
  have h5 (q : Pattern) (selected : d2274 q = 1) : d4566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4251 q = 1) : d67836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4251, d67836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4251, d67836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4252 q = 1) : d67837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4252, d67837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4252, d67837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4253 q = 1) : d67838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4253, d67838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4253, d67838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4254 q = 1) : d67839 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4254, d67839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4254, d67839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro2670 (p : Pattern) (selected : d4258 p = 1) : d67843 p = 1 := by
  have h0 (q : Pattern) (selected : d2133 q = 1) : d2133 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2142 q = 1) : d2142 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2162 q = 1) : d2162 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d2273 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro161 q selected
    | true =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro162 q selected
  have h4 (q : Pattern) (selected : d2274 q = 1) : d4566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d4251 q = 1) : d67836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4251, d67836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4251, d67836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4252 q = 1) : d67837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4252, d67837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4252, d67837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4253 q = 1) : d67838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4253, d67838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4253, d67838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d2286 q = 1) : d2286 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d2291 q = 1) : d2291 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d2293 q = 1) : d2293 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d2296 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro164 q selected
    | true =>
      simp only [d2296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro165 q selected
  have h13 (q : Pattern) (selected : d2297 q = 1) : d4571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2297, d4571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2297, d4571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4255 q = 1) : d67840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4255, d67840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4255, d67840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h15 (q : Pattern) (selected : d4256 q = 1) : d67841 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4256, d67841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4256, d67841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4257 q = 1) : d67842 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4257, d67842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4257, d67842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d4258 q = 1) : d67843 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4258, d67843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4258, d67843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro2671 (p : Pattern) (selected : d4265 p = 1) : d67850 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2293 q = 1) : d2293 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2296 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro164 q selected
    | true =>
      simp only [d2296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro165 q selected
  have h3 (q : Pattern) (selected : d2297 q = 1) : d4571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2297, d4571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2297, d4571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4255 q = 1) : d67840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4255, d67840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4255, d67840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4263 q = 1) : d67848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4263, d67848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4263, d67848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4264 q = 1) : d67849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4264, d67849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4264, d67849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4265 q = 1) : d67850 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4265, d67850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4265, d67850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2672 (p : Pattern) (selected : d4274 p = 1) : d67859 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2392 q = 1) : d2392 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2440 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro173 q selected
    | true =>
      simp only [d2440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro174 q selected
  have h3 (q : Pattern) (selected : d2441 q = 1) : d4586 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2441, d4586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2441, d4586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4271 q = 1) : d67856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4271, d67856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4271, d67856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4272 q = 1) : d67857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4272, d67857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4272, d67857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4273 q = 1) : d67858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4273, d67858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4273, d67858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4274 q = 1) : d67859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4274, d67859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4274, d67859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2673 (p : Pattern) (selected : d4280 p = 1) : d67865 p = 1 := by
  have h0 (q : Pattern) (selected : d2125 q = 1) : d2125 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4259 q = 1) : d67844 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4259, d67844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2669 q selected
    | true =>
      simp only [d4259, d67844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2670 q selected
  have h2 (q : Pattern) (selected : d2317 q = 1) : d2317 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d4260 q = 1) : d67845 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4260, d67845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4260, d67845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d4261 q = 1) : d67846 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4261, d67846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4261, d67846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4262 q = 1) : d67847 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4262, d67847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4262, d67847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4266 q = 1) : d67851 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4266, d67851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4266, d67851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2671 q selected
  have h8 (q : Pattern) (selected : d2326 q = 1) : d2326 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d4267 q = 1) : d67852 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4267, d67852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4267, d67852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4268 q = 1) : d67853 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4268, d67853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4268, d67853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d4269 q = 1) : d67854 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4269, d67854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4269, d67854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d4270 q = 1) : d67855 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4270, d67855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4270, d67855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4275 q = 1) : d67860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4275, d67860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4275, d67860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2672 q selected
  have h14 (q : Pattern) (selected : d2459 q = 1) : d2459 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d4276 q = 1) : d67861 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4276, d67861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4276, d67861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4277 q = 1) : d67862 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4277, d67862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d4277, d67862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d4278 q = 1) : d67863 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4278, d67863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d4278, d67863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d4279 q = 1) : d67864 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4279, d67864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d4279, d67864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d4280 q = 1) : d67865 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4280, d67865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4280, d67865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro2674 (p : Pattern) (selected : d4286 p = 1) : d67871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4281 q = 1) : d67866 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4281, d67866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4281, d67866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2673 q selected
  have h2 (q : Pattern) (selected : d4282 q = 1) : d67867 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4282, d67867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4282, d67867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4283 q = 1) : d67868 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4283, d67868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4283, d67868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4284 q = 1) : d67869 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4284, d67869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4284, d67869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4285 q = 1) : d67870 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4285, d67870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4285, d67870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4286 q = 1) : d67871 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4286, d67871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4286, d67871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2675 (p : Pattern) (selected : d4292 p = 1) : d67877 p = 1 := by
  have h0 (q : Pattern) (selected : d4133 q = 1) : d67718 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4133, d67718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2644 q selected
    | true =>
      simp only [d4133, d67718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2650 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d4170 q = 1) : d67755 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4170, d67755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4170, d67755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2656 q selected
  have h3 (q : Pattern) (selected : d4171 q = 1) : d67756 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4171, d67756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4171, d67756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4208 q = 1) : d67793 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4208, d67793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4208, d67793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2662 q selected
  have h5 (q : Pattern) (selected : d4209 q = 1) : d67794 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4209, d67794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4209, d67794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4210 q = 1) : d67795 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4210, d67795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4210, d67795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4247 q = 1) : d67832 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4247, d67832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4247, d67832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2668 q selected
  have h8 (q : Pattern) (selected : d4248 q = 1) : d67833 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4248, d67833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4248, d67833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4249 q = 1) : d67834 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4249, d67834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4249, d67834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4250 q = 1) : d67835 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4250, d67835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4250, d67835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4287 q = 1) : d67872 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4287, d67872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4287, d67872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2674 q selected
  have h12 (q : Pattern) (selected : d4288 q = 1) : d67873 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4288, d67873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4288, d67873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4289 q = 1) : d67874 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4289, d67874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4289, d67874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4290 q = 1) : d67875 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4290, d67875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4290, d67875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d4291 q = 1) : d67876 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d4291, d67876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4291, d67876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4292 q = 1) : d67877 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d4292, d67877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d4292, d67877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2676 (p : Pattern) (selected : d4298 p = 1) : d67883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4293 q = 1) : d67878 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d4293, d67878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2675 q selected
    | true =>
      simp only [d4293, d67878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4294 q = 1) : d67879 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d4294, d67879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4294, d67879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4295 q = 1) : d67880 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d4295, d67880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4295, d67880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4296 q = 1) : d67881 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d4296, d67881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4296, d67881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4297 q = 1) : d67882 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d4297, d67882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4297, d67882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4298 q = 1) : d67883 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d4298, d67883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4298, d67883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2677 (p : Pattern) (selected : d4304 p = 1) : d67889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4299 q = 1) : d67884 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d4299, d67884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2676 q selected
    | true =>
      simp only [d4299, d67884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4300 q = 1) : d67885 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d4300, d67885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4300, d67885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4301 q = 1) : d67886 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d4301, d67886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4301, d67886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4302 q = 1) : d67887 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d4302, d67887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4302, d67887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4303 q = 1) : d67888 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d4303, d67888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4303, d67888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4304 q = 1) : d67889 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d4304, d67889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4304, d67889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2678 (p : Pattern) (selected : d4310 p = 1) : d67895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4305 q = 1) : d67890 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d4305, d67890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2677 q selected
    | true =>
      simp only [d4305, d67890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4306 q = 1) : d67891 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d4306, d67891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4306, d67891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4307 q = 1) : d67892 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d4307, d67892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4307, d67892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4308 q = 1) : d67893 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d4308, d67893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4308, d67893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4309 q = 1) : d67894 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d4309, d67894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4309, d67894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4310 q = 1) : d67895 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d4310, d67895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4310, d67895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2679 (p : Pattern) (selected : d4316 p = 1) : d67901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4311 q = 1) : d67896 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d4311, d67896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2678 q selected
    | true =>
      simp only [d4311, d67896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4312 q = 1) : d67897 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d4312, d67897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4312, d67897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4313 q = 1) : d67898 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d4313, d67898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4313, d67898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4314 q = 1) : d67899 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d4314, d67899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4314, d67899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4315 q = 1) : d67900 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d4315, d67900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4315, d67900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4316 q = 1) : d67901 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d4316, d67901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4316, d67901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2680 (p : Pattern) (selected : d4322 p = 1) : d67907 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4317 q = 1) : d67902 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4317, d67902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2679 q selected
    | true =>
      simp only [d4317, d67902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4318 q = 1) : d67903 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4318, d67903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4318, d67903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4319 q = 1) : d67904 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4319, d67904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4319, d67904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4320 q = 1) : d67905 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4320, d67905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4320, d67905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4321 q = 1) : d67906 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4321, d67906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4321, d67906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4322 q = 1) : d67907 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4322, d67907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4322, d67907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2681 (p : Pattern) (selected : d4328 p = 1) : d67913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4323 q = 1) : d67908 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4323, d67908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2680 q selected
    | true =>
      simp only [d4323, d67908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4324 q = 1) : d67909 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4324, d67909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4324, d67909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4325 q = 1) : d67910 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4325, d67910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4325, d67910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4326 q = 1) : d67911 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4326, d67911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4326, d67911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4327 q = 1) : d67912 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4327, d67912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4327, d67912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4328 q = 1) : d67913 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4328, d67913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4328, d67913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2682 (p : Pattern) (selected : d4334 p = 1) : d67919 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d4329 q = 1) : d67914 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4329, d67914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2681 q selected
    | true =>
      simp only [d4329, d67914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4330 q = 1) : d67915 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4330, d67915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4330, d67915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4331 q = 1) : d67916 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4331, d67916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4331, d67916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4332 q = 1) : d67917 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4332, d67917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4332, d67917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4333 q = 1) : d67918 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4333, d67918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4333, d67918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4334 q = 1) : d67919 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4334, d67919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4334, d67919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2683 (p : Pattern) (selected : d4339 p = 0) : d68228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d157 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d4335 q = 0) : d68224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d68224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4335, d68224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4336 q = 0) : d68225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d68225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4336, d68225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4337 q = 0) : d68226 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4337, d68226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4337, d68226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4338 q = 0) : d68227 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4338, d68227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4338, d68227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4339 q = 0) : d68228 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4339, d68228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4339, d68228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2684 (p : Pattern) (selected : d4344 p = 0) : d68233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d157 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d4335 q = 0) : d68224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d68224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4335, d68224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4336 q = 0) : d68225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d68225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4336, d68225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4337 q = 0) : d68226 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4337, d68226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4337, d68226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4338 q = 0) : d68227 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4338, d68227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4338, d68227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d204 q = 0) : d52024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h9 (q : Pattern) (selected : d4340 q = 0) : d68229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d68229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4340, d68229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4341 q = 0) : d68230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d68230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4341, d68230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4342 q = 0) : d68231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d68231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4342, d68231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4343 q = 0) : d68232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d68232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4343, d68232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d4344 q = 0) : d68233 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4344, d68233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4344, d68233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2685 (p : Pattern) (selected : d4349 p = 0) : d68238 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d204 q = 0) : d52024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h2 (q : Pattern) (selected : d4340 q = 0) : d68229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d68229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4340, d68229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4341 q = 0) : d68230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d68230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4341, d68230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4342 q = 0) : d68231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d68231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4342, d68231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4343 q = 0) : d68232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d68232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4343, d68232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4349 q = 0) : d68238 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d68238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4349, d68238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2686 (p : Pattern) (selected : d4359 p = 0) : d68248 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d244 q = 0) : d52062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d52062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro224 q selected
    | true =>
      simp only [d244, d52062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
  have h2 (q : Pattern) (selected : d4355 q = 0) : d68244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d68244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4355, d68244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d84 q = 0) : d51936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85 q = 0) : d51937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4356 q = 0) : d68245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d68245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4356, d68245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4357 q = 0) : d68246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d68246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4357, d68246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4358 q = 0) : d68247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d68247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4358, d68247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4359 q = 0) : d68248 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d68248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4359, d68248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2687 (p : Pattern) (selected : d4365 p = 0) : d68254 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4345 q = 0) : d68234 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4345, d68234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2683 q selected
    | true =>
      simp only [d4345, d68234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2684 q selected
  have h2 (q : Pattern) (selected : d4346 q = 0) : d68235 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4346, d68235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4346, d68235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4347 q = 0) : d68236 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4347, d68236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4347, d68236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4348 q = 0) : d68237 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4348, d68237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4348, d68237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4350 q = 0) : d68239 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d68239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4350, d68239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2685 q selected
  have h6 (q : Pattern) (selected : d4351 q = 0) : d68240 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d68240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4351, d68240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4352 q = 0) : d68241 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d68241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4352, d68241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d4353 q = 0) : d68242 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d68242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4353, d68242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d4354 q = 0) : d68243 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4354, d68243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4354, d68243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4360 q = 0) : d68249 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d68249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4360, d68249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2686 q selected
  have h11 (q : Pattern) (selected : d4361 q = 0) : d68250 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d68250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4361, d68250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4362 q = 0) : d68251 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d68251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4362, d68251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d4363 q = 0) : d68252 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d68252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4363, d68252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d4364 q = 0) : d68253 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d68253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4364, d68253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4365 q = 0) : d68254 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4365, d68254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4365, d68254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2688 (p : Pattern) (selected : d4375 p = 0) : d68264 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d337 q = 0) : d52136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro238 q selected
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
  have h2 (q : Pattern) (selected : d4371 q = 0) : d68260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d68260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4371, d68260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370 q = 0) : d52138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371 q = 0) : d52139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4372 q = 0) : d68261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d68261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4372, d68261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4373 q = 0) : d68262 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4373, d68262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4373, d68262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4374 q = 0) : d68263 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4374, d68263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4374, d68263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4375 q = 0) : d68264 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4375, d68264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4375, d68264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2689 (p : Pattern) (selected : d4380 p = 0) : d68269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d337 q = 0) : d52136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro238 q selected
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
  have h2 (q : Pattern) (selected : d4371 q = 0) : d68260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d68260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4371, d68260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d370 q = 0) : d52138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d371 q = 0) : d52139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4372 q = 0) : d68261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d68261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4372, d68261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4373 q = 0) : d68262 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4373, d68262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4373, d68262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4374 q = 0) : d68263 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4374, d68263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4374, d68263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d386 q = 0) : d52154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro247 q selected
    | true =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
  have h9 (q : Pattern) (selected : d4376 q = 0) : d68265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d68265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4376, d68265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d390 q = 0) : d52156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d391 q = 0) : d52157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4377 q = 0) : d68266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d68266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4377, d68266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4378 q = 0) : d68267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4378, d68267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4378, d68267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4379 q = 0) : d68268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4379, d68268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4379, d68268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d4380 q = 0) : d68269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4380, d68269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4380, d68269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2690 (p : Pattern) (selected : d4385 p = 0) : d68274 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d386 q = 0) : d52154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro247 q selected
    | true =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
  have h2 (q : Pattern) (selected : d4376 q = 0) : d68265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d68265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4376, d68265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d390 q = 0) : d52156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d391 q = 0) : d52157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4377 q = 0) : d68266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d68266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4377, d68266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4378 q = 0) : d68267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4378, d68267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4378, d68267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4379 q = 0) : d68268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4379, d68268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4379, d68268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4385 q = 0) : d68274 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4385, d68274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4385, d68274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2691 (p : Pattern) (selected : d4395 p = 0) : d68284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d430 q = 0) : d52196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d430, d52196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro255 q selected
    | true =>
      simp only [d430, d52196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro224 q selected
  have h2 (q : Pattern) (selected : d4391 q = 0) : d68280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d68280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4391, d68280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d451 q = 0) : d52198 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, d52198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro224 q selected
    | true =>
      simp only [d451, d52198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d452 q = 0) : d52199 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d452, d52199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d452, d52199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4392 q = 0) : d68281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4392, d68281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4392, d68281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4393 q = 0) : d68282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4393, d68282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4393, d68282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4394 q = 0) : d68283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4394, d68283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4394, d68283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4395 q = 0) : d68284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4395, d68284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4395, d68284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2692 (p : Pattern) (selected : d4401 p = 0) : d68290 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4381 q = 0) : d68270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4381, d68270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2688 q selected
    | true =>
      simp only [d4381, d68270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2689 q selected
  have h2 (q : Pattern) (selected : d4382 q = 0) : d68271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4382, d68271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4382, d68271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4383 q = 0) : d68272 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4383, d68272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4383, d68272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4384 q = 0) : d68273 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4384, d68273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4384, d68273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4386 q = 0) : d68275 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d68275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4386, d68275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2690 q selected
  have h6 (q : Pattern) (selected : d4387 q = 0) : d68276 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d68276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4387, d68276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4388 q = 0) : d68277 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, d68277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4388, d68277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d4389 q = 0) : d68278 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, d68278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4389, d68278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d4390 q = 0) : d68279 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4390, d68279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4390, d68279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4396 q = 0) : d68285 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d68285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4396, d68285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2691 q selected
  have h11 (q : Pattern) (selected : d4397 q = 0) : d68286 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4397, d68286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4397, d68286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4398 q = 0) : d68287 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4398, d68287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4398, d68287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d4399 q = 0) : d68288 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4399, d68288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4399, d68288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d4400 q = 0) : d68289 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4400, d68289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4400, d68289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4401 q = 0) : d68290 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4401, d68290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4401, d68290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2693 (p : Pattern) (selected : d4407 p = 0) : d68296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96 q = 0) : d51948 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro199 q selected
  have h2 (q : Pattern) (selected : d97 q = 0) : d51949 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 0) : d51950 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 0) : d51951 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4366 q = 0) : d68255 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4366, d68255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4366, d68255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2687 q selected
  have h6 (q : Pattern) (selected : d4367 q = 0) : d68256 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4367, d68256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4367, d68256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4368 q = 0) : d68257 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4368, d68257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4368, d68257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4369 q = 0) : d68258 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4369, d68258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4369, d68258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4370 q = 0) : d68259 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4370, d68259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4370, d68259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4402 q = 0) : d68291 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4402, d68291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4402, d68291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2692 q selected
  have h11 (q : Pattern) (selected : d4403 q = 0) : d68292 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4403, d68292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4403, d68292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d4404 q = 0) : d68293 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4404, d68293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4404, d68293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4405 q = 0) : d68294 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4405, d68294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4405, d68294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4406 q = 0) : d68295 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4406, d68295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4406, d68295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d4407 q = 0) : d68296 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4407, d68296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4407, d68296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2694 (p : Pattern) (selected : d4412 p = 0) : d68301 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d561 q = 0) : d52308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro280 q selected
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
  have h2 (q : Pattern) (selected : d4408 q = 0) : d68297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d68297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4408, d68297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d603 q = 0) : d52310 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d604 q = 0) : d52311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4409 q = 0) : d68298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d68298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4409, d68298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4410 q = 0) : d68299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4410, d68299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4410, d68299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4411 q = 0) : d68300 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4411, d68300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4411, d68300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4412 q = 0) : d68301 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4412, d68301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4412, d68301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2695 (p : Pattern) (selected : d4417 p = 0) : d68306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d561 q = 0) : d52308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro280 q selected
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
  have h2 (q : Pattern) (selected : d4408 q = 0) : d68297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d68297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4408, d68297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d603 q = 0) : d52310 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d604 q = 0) : d52311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4409 q = 0) : d68298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d68298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4409, d68298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4410 q = 0) : d68299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4410, d68299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4410, d68299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4411 q = 0) : d68300 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4411, d68300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4411, d68300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d621 q = 0) : d52328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro293 q selected
    | true =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
  have h9 (q : Pattern) (selected : d4413 q = 0) : d68302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d68302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4413, d68302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d626 q = 0) : d52330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
    | true =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d627 q = 0) : d52331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4414 q = 0) : d68303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d68303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4414, d68303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4415 q = 0) : d68304 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4415, d68304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4415, d68304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4416 q = 0) : d68305 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4416, d68305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4416, d68305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d4417 q = 0) : d68306 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4417, d68306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4417, d68306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2696 (p : Pattern) (selected : d4422 p = 0) : d68311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d621 q = 0) : d52328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro293 q selected
    | true =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
  have h2 (q : Pattern) (selected : d4413 q = 0) : d68302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d68302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4413, d68302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d626 q = 0) : d52330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
    | true =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d627 q = 0) : d52331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4414 q = 0) : d68303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d68303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4414, d68303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4415 q = 0) : d68304 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4415, d68304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4415, d68304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4416 q = 0) : d68305 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4416, d68305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4416, d68305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4422 q = 0) : d68311 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4422, d68311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4422, d68311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2697 (p : Pattern) (selected : d4432 p = 0) : d68321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d690 q = 0) : d52394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d690, d52394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro304 q selected
    | true =>
      simp only [d690, d52394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro306 q selected
  have h2 (q : Pattern) (selected : d4428 q = 0) : d68317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d68317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4428, d68317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d720 q = 0) : d52401 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d720, d52401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro306 q selected
    | true =>
      simp only [d720, d52401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d721 q = 0) : d52402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d721, d52402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d721, d52402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4429 q = 0) : d68318 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4429, d68318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4429, d68318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4430 q = 0) : d68319 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4430, d68319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4430, d68319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4431 q = 0) : d68320 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4431, d68320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4431, d68320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4432 q = 0) : d68321 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4432, d68321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4432, d68321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2698 (p : Pattern) (selected : d4438 p = 0) : d68327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4418 q = 0) : d68307 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4418, d68307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2694 q selected
    | true =>
      simp only [d4418, d68307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2695 q selected
  have h2 (q : Pattern) (selected : d4419 q = 0) : d68308 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4419, d68308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4419, d68308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4420 q = 0) : d68309 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4420, d68309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4420, d68309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4421 q = 0) : d68310 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4421, d68310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4421, d68310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4423 q = 0) : d68312 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d68312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4423, d68312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2696 q selected
  have h6 (q : Pattern) (selected : d4424 q = 0) : d68313 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d68313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4424, d68313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4425 q = 0) : d68314 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, d68314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4425, d68314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d4426 q = 0) : d68315 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, d68315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4426, d68315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d4427 q = 0) : d68316 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4427, d68316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4427, d68316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4433 q = 0) : d68322 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d68322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4433, d68322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2697 q selected
  have h11 (q : Pattern) (selected : d4434 q = 0) : d68323 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4434, d68323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4434, d68323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4435 q = 0) : d68324 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4435, d68324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4435, d68324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d4436 q = 0) : d68325 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4436, d68325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4436, d68325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d4437 q = 0) : d68326 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4437, d68326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4437, d68326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4438 q = 0) : d68327 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4438, d68327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4438, d68327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2699 (p : Pattern) (selected : d4444 p = 0) : d68333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4439 q = 0) : d68328 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4439, d68328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4439, d68328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2698 q selected
  have h2 (q : Pattern) (selected : d4440 q = 0) : d68329 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4440, d68329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4440, d68329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4441 q = 0) : d68330 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4441, d68330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4441, d68330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4442 q = 0) : d68331 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4442, d68331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4442, d68331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4443 q = 0) : d68332 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4443, d68332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4443, d68332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4444 q = 0) : d68333 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4444, d68333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4444, d68333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2700 (p : Pattern) (selected : d4450 p = 0) : d68339 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d852 q = 0) : d52529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro338 q selected
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
  have h2 (q : Pattern) (selected : d4446 q = 0) : d68335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d68335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4446, d68335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d909 q = 0) : d52531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d910 q = 0) : d52532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4447 q = 0) : d68336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d68336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4447, d68336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4448 q = 0) : d68337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4448, d68337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4448, d68337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4449 q = 0) : d68338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4449, d68338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4449, d68338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4450 q = 0) : d68339 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4450, d68339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4450, d68339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2701 (p : Pattern) (selected : d4455 p = 0) : d68344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d852 q = 0) : d52529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro338 q selected
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
  have h2 (q : Pattern) (selected : d4446 q = 0) : d68335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d68335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4446, d68335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d909 q = 0) : d52531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d910 q = 0) : d52532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4447 q = 0) : d68336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d68336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4447, d68336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4448 q = 0) : d68337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4448, d68337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4448, d68337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4449 q = 0) : d68338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4449, d68338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4449, d68338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d927 q = 0) : d52549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro355 q selected
    | true =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
  have h9 (q : Pattern) (selected : d4451 q = 0) : d68340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d68340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4451, d68340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d932 q = 0) : d52551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
    | true =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d933 q = 0) : d52552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4452 q = 0) : d68341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d68341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4452, d68341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4453 q = 0) : d68342 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4453, d68342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4453, d68342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4454 q = 0) : d68343 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4454, d68343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4454, d68343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d4455 q = 0) : d68344 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4455, d68344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4455, d68344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2702 (p : Pattern) (selected : d4460 p = 0) : d68349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d927 q = 0) : d52549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro355 q selected
    | true =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
  have h2 (q : Pattern) (selected : d4451 q = 0) : d68340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d68340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4451, d68340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d932 q = 0) : d52551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
    | true =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d933 q = 0) : d52552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4452 q = 0) : d68341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d68341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4452, d68341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4453 q = 0) : d68342 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4453, d68342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4453, d68342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4454 q = 0) : d68343 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4454, d68343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4454, d68343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4460 q = 0) : d68349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4460, d68349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4460, d68349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2703 (p : Pattern) (selected : d4470 p = 0) : d68359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1012 q = 0) : d52631 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1012, d52631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro369 q selected
    | true =>
      simp only [d1012, d52631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro371 q selected
  have h2 (q : Pattern) (selected : d4466 q = 0) : d68355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d68355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4466, d68355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1053 q = 0) : d52638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1053, d52638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro371 q selected
    | true =>
      simp only [d1053, d52638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1054 q = 0) : d52639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1054, d52639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1054, d52639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4467 q = 0) : d68356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4467, d68356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4467, d68356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4468 q = 0) : d68357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4468, d68357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4468, d68357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4469 q = 0) : d68358 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4469, d68358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4469, d68358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4470 q = 0) : d68359 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4470, d68359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4470, d68359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2704 (p : Pattern) (selected : d4476 p = 0) : d68365 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4456 q = 0) : d68345 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4456, d68345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2700 q selected
    | true =>
      simp only [d4456, d68345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2701 q selected
  have h2 (q : Pattern) (selected : d4457 q = 0) : d68346 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4457, d68346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4457, d68346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4458 q = 0) : d68347 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4458, d68347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4458, d68347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4459 q = 0) : d68348 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4459, d68348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4459, d68348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4461 q = 0) : d68350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d68350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4461, d68350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2702 q selected
  have h6 (q : Pattern) (selected : d4462 q = 0) : d68351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d68351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4462, d68351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4463 q = 0) : d68352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, d68352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4463, d68352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d4464 q = 0) : d68353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, d68353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4464, d68353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d4465 q = 0) : d68354 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4465, d68354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4465, d68354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4471 q = 0) : d68360 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d68360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4471, d68360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2703 q selected
  have h11 (q : Pattern) (selected : d4472 q = 0) : d68361 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4472, d68361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4472, d68361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4473 q = 0) : d68362 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4473, d68362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4473, d68362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d4474 q = 0) : d68363 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4474, d68363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4474, d68363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d4475 q = 0) : d68364 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4475, d68364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4475, d68364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4476 q = 0) : d68365 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4476, d68365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4476, d68365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2705 (p : Pattern) (selected : d4482 p = 0) : d68371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4477 q = 0) : d68366 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4477, d68366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4477, d68366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2704 q selected
  have h2 (q : Pattern) (selected : d4478 q = 0) : d68367 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4478, d68367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4478, d68367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4479 q = 0) : d68368 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4479, d68368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4479, d68368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4480 q = 0) : d68369 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4480, d68369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4480, d68369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4481 q = 0) : d68370 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4481, d68370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4481, d68370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4482 q = 0) : d68371 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4482, d68371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4482, d68371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2706 (p : Pattern) (selected : d4489 p = 0) : d68378 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1228 q = 0) : d52809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro410 q selected
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
  have h2 (q : Pattern) (selected : d4485 q = 0) : d68374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d68374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4485, d68374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1320 q = 0) : d52811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1321 q = 0) : d52812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4486 q = 0) : d68375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d68375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4486, d68375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4487 q = 0) : d68376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4487, d68376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4487, d68376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4488 q = 0) : d68377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4488, d68377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4488, d68377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4489 q = 0) : d68378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4489, d68378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4489, d68378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2707 (p : Pattern) (selected : d4494 p = 0) : d68383 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1228 q = 0) : d52809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro410 q selected
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
  have h2 (q : Pattern) (selected : d4485 q = 0) : d68374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d68374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4485, d68374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1320 q = 0) : d52811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1321 q = 0) : d52812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4486 q = 0) : d68375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d68375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4486, d68375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4487 q = 0) : d68376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4487, d68376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4487, d68376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4488 q = 0) : d68377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4488, d68377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4488, d68377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1338 q = 0) : d52829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro431 q selected
    | true =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
  have h9 (q : Pattern) (selected : d4490 q = 0) : d68379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d68379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4490, d68379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1343 q = 0) : d52831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
    | true =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1344 q = 0) : d52832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4491 q = 0) : d68380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d68380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4491, d68380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4492 q = 0) : d68381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4492, d68381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4492, d68381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4493 q = 0) : d68382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4493, d68382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4493, d68382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d4494 q = 0) : d68383 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4494, d68383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4494, d68383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2708 (p : Pattern) (selected : d4499 p = 0) : d68388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1338 q = 0) : d52829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro431 q selected
    | true =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
  have h2 (q : Pattern) (selected : d4490 q = 0) : d68379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d68379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4490, d68379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1343 q = 0) : d52831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
    | true =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1344 q = 0) : d52832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4491 q = 0) : d68380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d68380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4491, d68380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4492 q = 0) : d68381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4492, d68381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4492, d68381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4493 q = 0) : d68382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4493, d68382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4493, d68382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4499 q = 0) : d68388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4499, d68388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4499, d68388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2709 (p : Pattern) (selected : d4509 p = 0) : d68398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1437 q = 0) : d52925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1437, d52925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro445 q selected
    | true =>
      simp only [d1437, d52925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro447 q selected
  have h2 (q : Pattern) (selected : d4505 q = 0) : d68394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d68394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4505, d68394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1487 q = 0) : d52932 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1487, d52932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro447 q selected
    | true =>
      simp only [d1487, d52932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1488 q = 0) : d52933 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1488, d52933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1488, d52933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4506 q = 0) : d68395 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4506, d68395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4506, d68395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4507 q = 0) : d68396 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4507, d68396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4507, d68396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4508 q = 0) : d68397 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4508, d68397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4508, d68397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4509 q = 0) : d68398 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4509, d68398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4509, d68398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2710 (p : Pattern) (selected : d4515 p = 0) : d68404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4495 q = 0) : d68384 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4495, d68384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2706 q selected
    | true =>
      simp only [d4495, d68384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2707 q selected
  have h2 (q : Pattern) (selected : d4496 q = 0) : d68385 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4496, d68385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4496, d68385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4497 q = 0) : d68386 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4497, d68386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4497, d68386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4498 q = 0) : d68387 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4498, d68387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4498, d68387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4500 q = 0) : d68389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d68389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4500, d68389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2708 q selected
  have h6 (q : Pattern) (selected : d4501 q = 0) : d68390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d68390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4501, d68390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4502 q = 0) : d68391 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, d68391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4502, d68391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d4503 q = 0) : d68392 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, d68392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4503, d68392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d4504 q = 0) : d68393 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4504, d68393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4504, d68393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4510 q = 0) : d68399 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d68399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4510, d68399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2709 q selected
  have h11 (q : Pattern) (selected : d4511 q = 0) : d68400 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4511, d68400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4511, d68400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4512 q = 0) : d68401 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4512, d68401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4512, d68401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d4513 q = 0) : d68402 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4513, d68402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4513, d68402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d4514 q = 0) : d68403 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4514, d68403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4514, d68403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4515 q = 0) : d68404 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4515, d68404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4515, d68404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2711 (p : Pattern) (selected : d4521 p = 0) : d68410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4516 q = 0) : d68405 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4516, d68405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4516, d68405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2710 q selected
  have h2 (q : Pattern) (selected : d4517 q = 0) : d68406 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4517, d68406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4517, d68406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4518 q = 0) : d68407 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4518, d68407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4518, d68407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4519 q = 0) : d68408 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4519, d68408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4519, d68408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4520 q = 0) : d68409 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4520, d68409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4520, d68409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4521 q = 0) : d68410 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4521, d68410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4521, d68410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2712 (p : Pattern) (selected : d4529 p = 0) : d68418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1683 q = 0) : d53124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro490 q selected
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
  have h2 (q : Pattern) (selected : d4525 q = 0) : d68414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d68414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4525, d68414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1797 q = 0) : d53126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1798 q = 0) : d53127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4526 q = 0) : d68415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d68415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4526, d68415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4527 q = 0) : d68416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4527, d68416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4527, d68416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4528 q = 0) : d68417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4528, d68417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4528, d68417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4529 q = 0) : d68418 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4529, d68418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4529, d68418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2713 (p : Pattern) (selected : d4534 p = 0) : d68423 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1683 q = 0) : d53124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro490 q selected
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
  have h2 (q : Pattern) (selected : d4525 q = 0) : d68414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d68414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4525, d68414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1797 q = 0) : d53126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1798 q = 0) : d53127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4526 q = 0) : d68415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d68415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4526, d68415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4527 q = 0) : d68416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4527, d68416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4527, d68416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4528 q = 0) : d68417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4528, d68417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4528, d68417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1815 q = 0) : d53144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro517 q selected
    | true =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
  have h9 (q : Pattern) (selected : d4530 q = 0) : d68419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d68419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4530, d68419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1820 q = 0) : d53146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
    | true =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1821 q = 0) : d53147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4531 q = 0) : d68420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d68420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4531, d68420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4532 q = 0) : d68421 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d68421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4532, d68421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4533 q = 0) : d68422 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d68422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4533, d68422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d4534 q = 0) : d68423 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4534, d68423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4534, d68423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2714 (p : Pattern) (selected : d4539 p = 0) : d68428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1815 q = 0) : d53144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro517 q selected
    | true =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
  have h2 (q : Pattern) (selected : d4530 q = 0) : d68419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d68419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4530, d68419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1820 q = 0) : d53146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
    | true =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1821 q = 0) : d53147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4531 q = 0) : d68420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d68420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4531, d68420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4532 q = 0) : d68421 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d68421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4532, d68421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4533 q = 0) : d68422 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d68422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4533, d68422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4539 q = 0) : d68428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4539, d68428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4539, d68428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2715 (p : Pattern) (selected : d4549 p = 0) : d68438 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1914 q = 0) : d53240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1914, d53240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro531 q selected
    | true =>
      simp only [d1914, d53240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro533 q selected
  have h2 (q : Pattern) (selected : d4545 q = 0) : d68434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d68434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4545, d68434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1964 q = 0) : d53247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1964, d53247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro533 q selected
    | true =>
      simp only [d1964, d53247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1965 q = 0) : d53248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1965, d53248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1965, d53248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4546 q = 0) : d68435 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4546, d68435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4546, d68435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4547 q = 0) : d68436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4547, d68436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4547, d68436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4548 q = 0) : d68437 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4548, d68437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4548, d68437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4549 q = 0) : d68438 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4549, d68438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4549, d68438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2716 (p : Pattern) (selected : d4555 p = 0) : d68444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4535 q = 0) : d68424 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4535, d68424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2712 q selected
    | true =>
      simp only [d4535, d68424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2713 q selected
  have h2 (q : Pattern) (selected : d4536 q = 0) : d68425 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4536, d68425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4536, d68425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4537 q = 0) : d68426 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4537, d68426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4537, d68426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4538 q = 0) : d68427 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4538, d68427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4538, d68427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4540 q = 0) : d68429 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d68429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4540, d68429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2714 q selected
  have h6 (q : Pattern) (selected : d4541 q = 0) : d68430 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d68430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4541, d68430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4542 q = 0) : d68431 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, d68431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4542, d68431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d4543 q = 0) : d68432 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, d68432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4543, d68432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d4544 q = 0) : d68433 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4544, d68433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4544, d68433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4550 q = 0) : d68439 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d68439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4550, d68439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2715 q selected
  have h11 (q : Pattern) (selected : d4551 q = 0) : d68440 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4551, d68440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4551, d68440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4552 q = 0) : d68441 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4552, d68441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4552, d68441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d4553 q = 0) : d68442 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4553, d68442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4553, d68442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d4554 q = 0) : d68443 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4554, d68443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4554, d68443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4555 q = 0) : d68444 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4555, d68444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4555, d68444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2717 (p : Pattern) (selected : d4561 p = 0) : d68450 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4556 q = 0) : d68445 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4556, d68445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4556, d68445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2716 q selected
  have h2 (q : Pattern) (selected : d4557 q = 0) : d68446 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4557, d68446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4557, d68446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4558 q = 0) : d68447 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4558, d68447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4558, d68447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4559 q = 0) : d68448 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4559, d68448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4559, d68448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4560 q = 0) : d68449 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4560, d68449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4560, d68449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4561 q = 0) : d68450 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4561, d68450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4561, d68450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2718 (p : Pattern) (selected : d4570 p = 0) : d68459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2162 q = 0) : d53441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro579 q selected
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
  have h2 (q : Pattern) (selected : d4566 q = 0) : d68455 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d68455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4566, d68455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2275 q = 0) : d53443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2276 q = 0) : d53444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4567 q = 0) : d68456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d68456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4567, d68456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4568 q = 0) : d68457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4568, d68457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4568, d68457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4569 q = 0) : d68458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4569, d68458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4569, d68458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4570 q = 0) : d68459 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4570, d68459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4570, d68459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2719 (p : Pattern) (selected : d4575 p = 0) : d68464 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2162 q = 0) : d53441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro579 q selected
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
  have h2 (q : Pattern) (selected : d4566 q = 0) : d68455 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d68455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4566, d68455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2275 q = 0) : d53443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2276 q = 0) : d53444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4567 q = 0) : d68456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d68456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4567, d68456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4568 q = 0) : d68457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4568, d68457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4568, d68457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4569 q = 0) : d68458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4569, d68458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4569, d68458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2293 q = 0) : d53461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro607 q selected
    | true =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
  have h9 (q : Pattern) (selected : d4571 q = 0) : d68460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d68460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d4571, d68460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d2298 q = 0) : d53463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
    | true =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d2299 q = 0) : d53464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4572 q = 0) : d68461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d68461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4572, d68461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4573 q = 0) : d68462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d68462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4573, d68462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4574 q = 0) : d68463 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d68463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4574, d68463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d4575 q = 0) : d68464 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4575, d68464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4575, d68464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2720 (p : Pattern) (selected : d4580 p = 0) : d68469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2293 q = 0) : d53461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro607 q selected
    | true =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
  have h2 (q : Pattern) (selected : d4571 q = 0) : d68460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d68460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4571, d68460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2298 q = 0) : d53463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
    | true =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2299 q = 0) : d53464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4572 q = 0) : d68461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d68461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4572, d68461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4573 q = 0) : d68462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d68462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4573, d68462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4574 q = 0) : d68463 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d68463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4574, d68463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4580 q = 0) : d68469 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4580, d68469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4580, d68469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2721 (p : Pattern) (selected : d4590 p = 0) : d68479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2392 q = 0) : d53557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2392, d53557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro621 q selected
    | true =>
      simp only [d2392, d53557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro623 q selected
  have h2 (q : Pattern) (selected : d4586 q = 0) : d68475 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d68475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4586, d68475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2442 q = 0) : d53564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2442, d53564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro623 q selected
    | true =>
      simp only [d2442, d53564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2443 q = 0) : d53565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2443, d53565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2443, d53565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4587 q = 0) : d68476 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4587, d68476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4587, d68476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4588 q = 0) : d68477 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4588, d68477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4588, d68477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4589 q = 0) : d68478 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4589, d68478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4589, d68478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d4590 q = 0) : d68479 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4590, d68479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4590, d68479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2722 (p : Pattern) (selected : d4596 p = 0) : d68485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4576 q = 0) : d68465 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4576, d68465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2718 q selected
    | true =>
      simp only [d4576, d68465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2719 q selected
  have h2 (q : Pattern) (selected : d4577 q = 0) : d68466 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4577, d68466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4577, d68466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4578 q = 0) : d68467 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4578, d68467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4578, d68467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4579 q = 0) : d68468 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4579, d68468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4579, d68468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4581 q = 0) : d68470 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d68470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4581, d68470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2720 q selected
  have h6 (q : Pattern) (selected : d4582 q = 0) : d68471 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d68471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4582, d68471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d4583 q = 0) : d68472 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, d68472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4583, d68472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d4584 q = 0) : d68473 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, d68473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d4584, d68473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d4585 q = 0) : d68474 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4585, d68474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4585, d68474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4591 q = 0) : d68480 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d68480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4591, d68480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2721 q selected
  have h11 (q : Pattern) (selected : d4592 q = 0) : d68481 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4592, d68481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4592, d68481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d4593 q = 0) : d68482 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4593, d68482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d4593, d68482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d4594 q = 0) : d68483 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4594, d68483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d4594, d68483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d4595 q = 0) : d68484 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4595, d68484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d4595, d68484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d4596 q = 0) : d68485 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4596, d68485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d4596, d68485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2723 (p : Pattern) (selected : d4602 p = 0) : d68491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4597 q = 0) : d68486 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4597, d68486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4597, d68486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2722 q selected
  have h2 (q : Pattern) (selected : d4598 q = 0) : d68487 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4598, d68487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4598, d68487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d4599 q = 0) : d68488 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4599, d68488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4599, d68488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4600 q = 0) : d68489 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4600, d68489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4600, d68489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d4601 q = 0) : d68490 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4601, d68490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4601, d68490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4602 q = 0) : d68491 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4602, d68491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4602, d68491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2724 (p : Pattern) (selected : d4608 p = 0) : d68497 p = 1 := by
  have h0 (q : Pattern) (selected : d4445 q = 0) : d68334 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4445, d68334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2693 q selected
    | true =>
      simp only [d4445, d68334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2699 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d4483 q = 0) : d68372 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4483, d68372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4483, d68372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2705 q selected
  have h3 (q : Pattern) (selected : d4484 q = 0) : d68373 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4484, d68373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d4484, d68373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d4522 q = 0) : d68411 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4522, d68411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4522, d68411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2711 q selected
  have h5 (q : Pattern) (selected : d4523 q = 0) : d68412 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4523, d68412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4523, d68412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d4524 q = 0) : d68413 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4524, d68413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4524, d68413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d4562 q = 0) : d68451 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4562, d68451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4562, d68451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2717 q selected
  have h8 (q : Pattern) (selected : d4563 q = 0) : d68452 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4563, d68452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4563, d68452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d4564 q = 0) : d68453 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4564, d68453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4564, d68453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d4565 q = 0) : d68454 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4565, d68454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d4565, d68454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d4603 q = 0) : d68492 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4603, d68492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4603, d68492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2723 q selected
  have h12 (q : Pattern) (selected : d4604 q = 0) : d68493 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4604, d68493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4604, d68493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d4605 q = 0) : d68494 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4605, d68494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4605, d68494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d4606 q = 0) : d68495 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4606, d68495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4606, d68495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d4607 q = 0) : d68496 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d4607, d68496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d4607, d68496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d4608 q = 0) : d68497 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d4608, d68497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d4608, d68497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2725 (p : Pattern) (selected : d4614 p = 0) : d68503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4609 q = 0) : d68498 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d4609, d68498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2724 q selected
    | true =>
      simp only [d4609, d68498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4610 q = 0) : d68499 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d4610, d68499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4610, d68499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4611 q = 0) : d68500 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d4611, d68500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4611, d68500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4612 q = 0) : d68501 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d4612, d68501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4612, d68501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4613 q = 0) : d68502 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d4613, d68502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4613, d68502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4614 q = 0) : d68503 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d4614, d68503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4614, d68503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2726 (p : Pattern) (selected : d4620 p = 0) : d68509 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4615 q = 0) : d68504 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d4615, d68504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2725 q selected
    | true =>
      simp only [d4615, d68504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4616 q = 0) : d68505 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d4616, d68505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4616, d68505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4617 q = 0) : d68506 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d4617, d68506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4617, d68506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4618 q = 0) : d68507 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d4618, d68507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4618, d68507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4619 q = 0) : d68508 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d4619, d68508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4619, d68508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4620 q = 0) : d68509 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d4620, d68509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4620, d68509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2727 (p : Pattern) (selected : d4626 p = 0) : d68515 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4621 q = 0) : d68510 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d4621, d68510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2726 q selected
    | true =>
      simp only [d4621, d68510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4622 q = 0) : d68511 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d4622, d68511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4622, d68511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4623 q = 0) : d68512 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d4623, d68512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4623, d68512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4624 q = 0) : d68513 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d4624, d68513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4624, d68513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4625 q = 0) : d68514 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d4625, d68514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4625, d68514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4626 q = 0) : d68515 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d4626, d68515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4626, d68515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2728 (p : Pattern) (selected : d4632 p = 0) : d68521 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4627 q = 0) : d68516 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d4627, d68516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2727 q selected
    | true =>
      simp only [d4627, d68516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4628 q = 0) : d68517 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d4628, d68517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4628, d68517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4629 q = 0) : d68518 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d4629, d68518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4629, d68518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4630 q = 0) : d68519 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d4630, d68519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4630, d68519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4631 q = 0) : d68520 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d4631, d68520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4631, d68520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4632 q = 0) : d68521 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d4632, d68521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4632, d68521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2729 (p : Pattern) (selected : d4638 p = 0) : d68527 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4633 q = 0) : d68522 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4633, d68522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2728 q selected
    | true =>
      simp only [d4633, d68522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4634 q = 0) : d68523 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4634, d68523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4634, d68523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4635 q = 0) : d68524 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4635, d68524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4635, d68524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4636 q = 0) : d68525 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4636, d68525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4636, d68525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4637 q = 0) : d68526 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4637, d68526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4637, d68526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4638 q = 0) : d68527 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4638, d68527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4638, d68527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2730 (p : Pattern) (selected : d4644 p = 0) : d68533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4639 q = 0) : d68528 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4639, d68528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2729 q selected
    | true =>
      simp only [d4639, d68528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4640 q = 0) : d68529 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4640, d68529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4640, d68529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4641 q = 0) : d68530 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4641, d68530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4641, d68530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4642 q = 0) : d68531 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4642, d68531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4642, d68531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4643 q = 0) : d68532 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4643, d68532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4643, d68532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4644 q = 0) : d68533 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4644, d68533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4644, d68533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2731 (p : Pattern) (selected : d4650 p = 0) : d68539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4645 q = 0) : d68534 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4645, d68534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2730 q selected
    | true =>
      simp only [d4645, d68534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d4646 q = 0) : d68535 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4646, d68535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d4646, d68535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d4647 q = 0) : d68536 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4647, d68536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d4647, d68536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d4648 q = 0) : d68537 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4648, d68537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d4648, d68537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d4649 q = 0) : d68538 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4649, d68538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d4649, d68538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d4650 q = 0) : d68539 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4650, d68539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d4650, d68539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2732 (p : Pattern) (selected : d4650 p = 1) : d4650 p = 1 := by
  have h0 (q : Pattern) (selected : d4650 q = 1) : d4650 q = 1 := by
    exact selected
  exact h0 p selected
theorem eqIntro2733 (p : Pattern) (selected : d3147 p = 2) : d53647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d105 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro658 q selected
  have h2 (q : Pattern) (selected : d106 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d112 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro658 q selected
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro659 q selected
  have h4 (q : Pattern) (selected : d113 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d114 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212 q = 2) : d112 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212, d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro672 q selected
    | true =>
      simp only [d212, d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro677 q selected
  have h7 (q : Pattern) (selected : d3143 q = 2) : d113 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3143, d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3143, d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3144 q = 2) : d53637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3144, d53637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3144, d53637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3145 q = 2) : d53638 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3145, d53638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3145, d53638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d221 q = 2) : d407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d221, d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d221, d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro679 q selected
  have h11 (q : Pattern) (selected : d222 q = 2) : d53639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222, d53639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222, d53639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223 q = 2) : d53640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223, d53640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223, d53640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d224 q = 2) : d53641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d224, d53641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d224, d53641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3146 q = 2) : d53642 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3146, d53642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3146, d53642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d269 q = 2) : d463 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269, d463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d269, d463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro686 q selected
  have h16 (q : Pattern) (selected : d270 q = 2) : d53643 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270, d53643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d270, d53643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d271 q = 2) : d53644 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271, d53644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d271, d53644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d272 q = 2) : d53645 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d272, d53645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d272, d53645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d273 q = 2) : d53646 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d273, d53646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d273, d53646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3147 q = 2) : d53647 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3147, d53647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3147, d53647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro2734 (p : Pattern) (selected : d3164 p = 2) : d53671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d285 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro688 q selected
  have h2 (q : Pattern) (selected : d286 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro688 q selected
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro689 q selected
  have h4 (q : Pattern) (selected : d293 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d294 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d396 q = 2) : d292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d396, d292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro702 q selected
    | true =>
      simp only [d396, d292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro707 q selected
  have h7 (q : Pattern) (selected : d3153 q = 2) : d293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3153, d293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3153, d293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3154 q = 2) : d53653 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3154, d53653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3154, d53653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3155 q = 2) : d53654 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3155, d53654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3155, d53654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d405 q = 2) : d53656 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d405, d53656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d405, d53656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro709 q selected
  have h11 (q : Pattern) (selected : d3156 q = 2) : d53657 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3156, d53657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3156, d53657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d3157 q = 2) : d53658 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3157, d53658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3157, d53658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d3158 q = 2) : d53659 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3158, d53659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3158, d53659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3159 q = 2) : d53660 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3159, d53660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3159, d53660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d457 q = 2) : d53666 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d457, d53666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d457, d53666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro717 q selected
  have h16 (q : Pattern) (selected : d3160 q = 2) : d53667 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3160, d53667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3160, d53667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d3161 q = 2) : d53668 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3161, d53668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d3161, d53668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d3162 q = 2) : d53669 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3162, d53669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d3162, d53669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d3163 q = 2) : d53670 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3163, d53670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d3163, d53670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3164 q = 2) : d53671 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3164, d53671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3164, d53671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro2735 (p : Pattern) (selected : d3170 p = 2) : d53677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d96 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro657 q selected
  have h2 (q : Pattern) (selected : d97 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3148 q = 2) : d53648 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3148, d53648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3148, d53648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2733 q selected
  have h6 (q : Pattern) (selected : d3149 q = 2) : d53649 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3149, d53649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3149, d53649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3150 q = 2) : d53650 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3150, d53650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3150, d53650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d3151 q = 2) : d53651 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3151, d53651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3151, d53651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3152 q = 2) : d53652 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3152, d53652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3152, d53652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3165 q = 2) : d53672 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3165, d53672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3165, d53672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2734 q selected
  have h11 (q : Pattern) (selected : d3166 q = 2) : d53673 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3166, d53673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3166, d53673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d3167 q = 2) : d53674 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3167, d53674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3167, d53674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3168 q = 2) : d53675 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3168, d53675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3168, d53675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3169 q = 2) : d53676 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3169, d53676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3169, d53676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3170 q = 2) : d53677 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3170, d53677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3170, d53677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2736 (p : Pattern) (selected : d3182 p = 2) : d53697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d498 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro725 q selected
  have h2 (q : Pattern) (selected : d499 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d508 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro725 q selected
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro728 q selected
  have h4 (q : Pattern) (selected : d509 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d510 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d632 q = 2) : d508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d632, d508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro746 q selected
    | true =>
      simp only [d632, d508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro754 q selected
  have h7 (q : Pattern) (selected : d3171 q = 2) : d509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3171, d509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3171, d509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3172 q = 2) : d53678 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3172, d53678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3172, d53678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3173 q = 2) : d53679 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3173, d53679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3173, d53679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d652 q = 2) : d53681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d652, d53681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d652, d53681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro757 q selected
  have h11 (q : Pattern) (selected : d3174 q = 2) : d53682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3174, d53682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3174, d53682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d3175 q = 2) : d53683 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3175, d53683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3175, d53683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d3176 q = 2) : d53684 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3176, d53684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3176, d53684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3177 q = 2) : d53685 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3177, d53685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3177, d53685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d726 q = 2) : d53692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d726, d53692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d726, d53692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro770 q selected
  have h16 (q : Pattern) (selected : d3178 q = 2) : d53693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3178, d53693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3178, d53693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d3179 q = 2) : d53694 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3179, d53694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d3179, d53694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d3180 q = 2) : d53695 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3180, d53695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d3180, d53695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d3181 q = 2) : d53696 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3181, d53696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d3181, d53696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3182 q = 2) : d53697 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3182, d53697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3182, d53697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro2737 (p : Pattern) (selected : d3188 p = 2) : d53703 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3183 q = 2) : d53698 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3183, d53698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3183, d53698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2736 q selected
  have h2 (q : Pattern) (selected : d3184 q = 2) : d53699 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3184, d53699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3184, d53699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3185 q = 2) : d53700 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3185, d53700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3185, d53700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3186 q = 2) : d53701 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3186, d53701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3186, d53701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3187 q = 2) : d53702 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3187, d53702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3187, d53702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3188 q = 2) : d53703 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3188, d53703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3188, d53703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2738 (p : Pattern) (selected : d3201 p = 2) : d53724 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d790 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro783 q selected
  have h2 (q : Pattern) (selected : d791 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d800 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro783 q selected
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro786 q selected
  have h4 (q : Pattern) (selected : d801 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d802 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d938 q = 2) : d800 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d938, d800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro808 q selected
    | true =>
      simp only [d938, d800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro816 q selected
  have h7 (q : Pattern) (selected : d3190 q = 2) : d801 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3190, d801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3190, d801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3191 q = 2) : d53705 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3191, d53705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3191, d53705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3192 q = 2) : d53706 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3192, d53706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3192, d53706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d958 q = 2) : d53708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d958, d53708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d958, d53708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro819 q selected
  have h11 (q : Pattern) (selected : d3193 q = 2) : d53709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3193, d53709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3193, d53709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d3194 q = 2) : d53710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3194, d53710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3194, d53710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d3195 q = 2) : d53711 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3195, d53711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3195, d53711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3196 q = 2) : d53712 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3196, d53712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3196, d53712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d1059 q = 2) : d53719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1059, d53719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1059, d53719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro837 q selected
  have h16 (q : Pattern) (selected : d3197 q = 2) : d53720 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3197, d53720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3197, d53720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d3198 q = 2) : d53721 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3198, d53721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d3198, d53721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d3199 q = 2) : d53722 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3199, d53722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d3199, d53722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d3200 q = 2) : d53723 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3200, d53723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d3200, d53723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3201 q = 2) : d53724 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3201, d53724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3201, d53724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro2739 (p : Pattern) (selected : d3207 p = 2) : d53730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3202 q = 2) : d53725 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3202, d53725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3202, d53725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2738 q selected
  have h2 (q : Pattern) (selected : d3203 q = 2) : d53726 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3203, d53726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3203, d53726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3204 q = 2) : d53727 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3204, d53727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3204, d53727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3205 q = 2) : d53728 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3205, d53728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3205, d53728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3206 q = 2) : d53729 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3206, d53729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3206, d53729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3207 q = 2) : d53730 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3207, d53730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3207, d53730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2740 (p : Pattern) (selected : d3221 p = 2) : d53752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1169 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro855 q selected
  have h2 (q : Pattern) (selected : d1170 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1179 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro855 q selected
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro858 q selected
  have h4 (q : Pattern) (selected : d1180 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1181 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1349 q = 2) : d1179 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1349, d1179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro884 q selected
    | true =>
      simp only [d1349, d1179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro892 q selected
  have h7 (q : Pattern) (selected : d3210 q = 2) : d1180 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3210, d1180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3210, d1180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3211 q = 2) : d53733 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3211, d53733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3211, d53733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3212 q = 2) : d53734 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3212, d53734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3212, d53734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1369 q = 2) : d53736 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1369, d53736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1369, d53736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro895 q selected
  have h11 (q : Pattern) (selected : d3213 q = 2) : d53737 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3213, d53737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3213, d53737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d3214 q = 2) : d53738 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3214, d53738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3214, d53738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d3215 q = 2) : d53739 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3215, d53739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3215, d53739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3216 q = 2) : d53740 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3216, d53740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3216, d53740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d1493 q = 2) : d53747 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1493, d53747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1493, d53747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro913 q selected
  have h16 (q : Pattern) (selected : d3217 q = 2) : d53748 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3217, d53748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3217, d53748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d3218 q = 2) : d53749 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3218, d53749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d3218, d53749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d3219 q = 2) : d53750 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3219, d53750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d3219, d53750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d3220 q = 2) : d53751 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3220, d53751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d3220, d53751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3221 q = 2) : d53752 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3221, d53752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3221, d53752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro2741 (p : Pattern) (selected : d3227 p = 2) : d53758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3222 q = 2) : d53753 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3222, d53753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3222, d53753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2740 q selected
  have h2 (q : Pattern) (selected : d3223 q = 2) : d53754 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3223, d53754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3223, d53754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3224 q = 2) : d53755 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3224, d53755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3224, d53755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3225 q = 2) : d53756 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3225, d53756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3225, d53756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3226 q = 2) : d53757 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3226, d53757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3226, d53757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3227 q = 2) : d53758 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3227, d53758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3227, d53758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2742 (p : Pattern) (selected : d3242 p = 2) : d53781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1630 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro937 q selected
  have h2 (q : Pattern) (selected : d1631 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1640 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro937 q selected
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro940 q selected
  have h4 (q : Pattern) (selected : d1641 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1642 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1826 q = 2) : d1640 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1826, d1640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro970 q selected
    | true =>
      simp only [d1826, d1640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro978 q selected
  have h7 (q : Pattern) (selected : d3231 q = 2) : d1641 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3231, d1641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3231, d1641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3232 q = 2) : d53762 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3232, d53762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3232, d53762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3233 q = 2) : d53763 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3233, d53763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3233, d53763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1846 q = 2) : d53765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1846, d53765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1846, d53765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro981 q selected
  have h11 (q : Pattern) (selected : d3234 q = 2) : d53766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3234, d53766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3234, d53766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d3235 q = 2) : d53767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3235, d53767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3235, d53767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d3236 q = 2) : d53768 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3236, d53768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3236, d53768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3237 q = 2) : d53769 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3237, d53769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3237, d53769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d1970 q = 2) : d53776 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1970, d53776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1970, d53776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro999 q selected
  have h16 (q : Pattern) (selected : d3238 q = 2) : d53777 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3238, d53777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3238, d53777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d3239 q = 2) : d53778 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3239, d53778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d3239, d53778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d3240 q = 2) : d53779 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3240, d53779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d3240, d53779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d3241 q = 2) : d53780 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3241, d53780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d3241, d53780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3242 q = 2) : d53781 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3242, d53781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3242, d53781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro2743 (p : Pattern) (selected : d3248 p = 2) : d53787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3243 q = 2) : d53782 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3243, d53782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3243, d53782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2742 q selected
  have h2 (q : Pattern) (selected : d3244 q = 2) : d53783 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3244, d53783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3244, d53783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3245 q = 2) : d53784 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3245, d53784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3245, d53784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3246 q = 2) : d53785 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3246, d53785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3246, d53785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3247 q = 2) : d53786 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3247, d53786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3247, d53786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3248 q = 2) : d53787 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3248, d53787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3248, d53787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2744 (p : Pattern) (selected : d3264 p = 2) : d53811 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2113 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1026 q selected
  have h2 (q : Pattern) (selected : d2114 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2123 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1026 q selected
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1029 q selected
  have h4 (q : Pattern) (selected : d2124 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2125 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2304 q = 2) : d2123 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2304, d2123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1060 q selected
    | true =>
      simp only [d2304, d2123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1068 q selected
  have h7 (q : Pattern) (selected : d3253 q = 2) : d2124 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3253, d2124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3253, d2124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3254 q = 2) : d53792 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3254, d53792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3254, d53792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3255 q = 2) : d53793 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3255, d53793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3255, d53793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2324 q = 2) : d53795 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2324, d53795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2324, d53795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1071 q selected
  have h11 (q : Pattern) (selected : d3256 q = 2) : d53796 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3256, d53796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3256, d53796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d3257 q = 2) : d53797 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3257, d53797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3257, d53797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d3258 q = 2) : d53798 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3258, d53798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3258, d53798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3259 q = 2) : d53799 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3259, d53799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3259, d53799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d2448 q = 2) : d53806 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2448, d53806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2448, d53806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1089 q selected
  have h16 (q : Pattern) (selected : d3260 q = 2) : d53807 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3260, d53807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3260, d53807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d3261 q = 2) : d53808 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3261, d53808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d3261, d53808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d3262 q = 2) : d53809 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3262, d53809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d3262, d53809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d3263 q = 2) : d53810 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3263, d53810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d3263, d53810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3264 q = 2) : d53811 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3264, d53811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3264, d53811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro2745 (p : Pattern) (selected : d3270 p = 2) : d53817 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3265 q = 2) : d53812 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3265, d53812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3265, d53812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2744 q selected
  have h2 (q : Pattern) (selected : d3266 q = 2) : d53813 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3266, d53813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3266, d53813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3267 q = 2) : d53814 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3267, d53814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3267, d53814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3268 q = 2) : d53815 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3268, d53815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3268, d53815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3269 q = 2) : d53816 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3269, d53816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3269, d53816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3270 q = 2) : d53817 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3270, d53817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3270, d53817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2746 (p : Pattern) (selected : d3276 p = 2) : d53823 p = 1 := by
  have h0 (q : Pattern) (selected : d3189 q = 2) : d53704 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3189, d53704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2735 q selected
    | true =>
      simp only [d3189, d53704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2737 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d3208 q = 2) : d53731 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3208, d53731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3208, d53731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2739 q selected
  have h3 (q : Pattern) (selected : d3209 q = 2) : d53732 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3209, d53732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3209, d53732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3228 q = 2) : d53759 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3228, d53759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3228, d53759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2741 q selected
  have h5 (q : Pattern) (selected : d3229 q = 2) : d53760 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3229, d53760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3229, d53760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3230 q = 2) : d53761 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3230, d53761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3230, d53761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3249 q = 2) : d53788 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3249, d53788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3249, d53788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2743 q selected
  have h8 (q : Pattern) (selected : d3250 q = 2) : d53789 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3250, d53789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3250, d53789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3251 q = 2) : d53790 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3251, d53790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3251, d53790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3252 q = 2) : d53791 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3252, d53791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3252, d53791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3271 q = 2) : d53818 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3271, d53818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3271, d53818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2745 q selected
  have h12 (q : Pattern) (selected : d3272 q = 2) : d53819 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3272, d53819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3272, d53819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3273 q = 2) : d53820 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3273, d53820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3273, d53820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3274 q = 2) : d53821 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3274, d53821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3274, d53821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3275 q = 2) : d53822 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3275, d53822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3275, d53822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3276 q = 2) : d53823 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3276, d53823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3276, d53823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2747 (p : Pattern) (selected : d3282 p = 2) : d53829 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3277 q = 2) : d53824 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3277, d53824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2746 q selected
    | true =>
      simp only [d3277, d53824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3278 q = 2) : d53825 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3278, d53825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3278, d53825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3279 q = 2) : d53826 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3279, d53826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3279, d53826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3280 q = 2) : d53827 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3280, d53827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3280, d53827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3281 q = 2) : d53828 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3281, d53828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3281, d53828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3282 q = 2) : d53829 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3282, d53829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3282, d53829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2748 (p : Pattern) (selected : d3288 p = 2) : d53835 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3283 q = 2) : d53830 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3283, d53830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2747 q selected
    | true =>
      simp only [d3283, d53830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3284 q = 2) : d53831 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3284, d53831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3284, d53831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3285 q = 2) : d53832 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3285, d53832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3285, d53832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3286 q = 2) : d53833 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3286, d53833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3286, d53833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3287 q = 2) : d53834 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3287, d53834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3287, d53834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3288 q = 2) : d53835 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3288, d53835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3288, d53835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2749 (p : Pattern) (selected : d3294 p = 2) : d53841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3289 q = 2) : d53836 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3289, d53836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2748 q selected
    | true =>
      simp only [d3289, d53836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3290 q = 2) : d53837 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3290, d53837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3290, d53837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3291 q = 2) : d53838 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3291, d53838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3291, d53838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3292 q = 2) : d53839 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3292, d53839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3292, d53839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3293 q = 2) : d53840 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d3293, d53840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3293, d53840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3294 q = 2) : d53841 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d3294, d53841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3294, d53841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
