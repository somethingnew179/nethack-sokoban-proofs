import NetHack.Soko22Hazard87.AndIntroBlocks0384
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro96250 (p : Pattern) (ha : d271214 p = 1) (hb : d338632 p = 1) : d351427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271214 q = 1) (hb : d338627 q = 1) : d351422 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d338627, d351422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96249 q ha hb
    | true =>
      simp only [d338627, d351422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d338628 q = 1) : d351423 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d338628, d351423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338628, d351423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271214 q = 1) (hb : d338629 q = 1) : d351424 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d338629, d351424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338629, d351424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271214 q = 1) (hb : d338630 q = 1) : d351425 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d338630, d351425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338630, d351425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d338631 q = 1) : d351426 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d338631, d351426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338631, d351426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d338632 q = 1) : d351427 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d338632, d351427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338632, d351427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96251 (p : Pattern) (ha : d271214 p = 1) (hb : d338638 p = 1) : d351433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271214 q = 1) (hb : d338633 q = 1) : d351428 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d338633, d351428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96250 q ha hb
    | true =>
      simp only [d338633, d351428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d338634 q = 1) : d351429 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d338634, d351429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338634, d351429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271214 q = 1) (hb : d338635 q = 1) : d351430 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d338635, d351430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338635, d351430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271214 q = 1) (hb : d338636 q = 1) : d351431 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d338636, d351431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338636, d351431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d338637 q = 1) : d351432 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d338637, d351432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338637, d351432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d338638 q = 1) : d351433 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d338638, d351433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338638, d351433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96252 (p : Pattern) (ha : d271214 p = 1) (hb : d338644 p = 1) : d351439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271214 q = 1) (hb : d338639 q = 1) : d351434 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d338639, d351434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96251 q ha hb
    | true =>
      simp only [d338639, d351434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d338640 q = 1) : d351435 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d338640, d351435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338640, d351435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271214 q = 1) (hb : d338641 q = 1) : d351436 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d338641, d351436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338641, d351436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271214 q = 1) (hb : d338642 q = 1) : d351437 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d338642, d351437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338642, d351437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d338643 q = 1) : d351438 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d338643, d351438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338643, d351438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d338644 q = 1) : d351439 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d338644, d351439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338644, d351439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96253 (p : Pattern) (ha : d271214 p = 1) (hb : d338650 p = 1) : d351445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271214 q = 1) (hb : d338645 q = 1) : d351440 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d338645, d351440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96252 q ha hb
    | true =>
      simp only [d338645, d351440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d338646 q = 1) : d351441 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d338646, d351441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338646, d351441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271214 q = 1) (hb : d338647 q = 1) : d351442 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d338647, d351442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338647, d351442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271214 q = 1) (hb : d338648 q = 1) : d351443 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d338648, d351443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338648, d351443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d338649 q = 1) : d351444 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d338649, d351444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338649, d351444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d338650 q = 1) : d351445 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d338650, d351445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338650, d351445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96254 (p : Pattern) (ha : d306197 p = 1) (hb : d349580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d306186 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306064 q = 1) (hb : d349516 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306064, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95892 q ha hb
    | true =>
      simp only [d306064, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d306187 q = 1) (hb : d349576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306187, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d306187, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d306193 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d306194 q = 1) (hb : d349577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306194, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d306194, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306195 q = 1) (hb : d349578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306195, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306195, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306196 q = 1) (hb : d349579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306196, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306196, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306197 q = 1) (hb : d349580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306197, d349580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306197, d349580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96255 (p : Pattern) (ha : d306216 p = 1) (hb : d349587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306144 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306150 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306064 q = 1) (hb : d349516 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306064, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95892 q ha hb
    | true =>
      simp only [d306064, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d306187 q = 1) (hb : d349576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306187, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306187, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d306193 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306194 q = 1) (hb : d349577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306194, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306194, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d306195 q = 1) (hb : d349578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306195, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306195, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306196 q = 1) (hb : d349579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306196, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306196, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d306202 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306206 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d306208 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306071 q = 1) (hb : d349523 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306071, d349523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95894 q ha hb
    | true =>
      simp only [d306071, d349523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d306209 q = 1) (hb : d349583 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306209, d349583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d306209, d349583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306212 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306213 q = 1) (hb : d349584 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306213, d349584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306213, d349584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306214 q = 1) (hb : d349585 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306214, d349585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d306214, d349585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d306215 q = 1) (hb : d349586 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306215, d349586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d306215, d349586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d306216 q = 1) (hb : d349587 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306216, d349587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306216, d349587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96256 (p : Pattern) (ha : d306225 p = 1) (hb : d351235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306208 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306071 q = 1) (hb : d349523 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306071, d349523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95894 q ha hb
    | true =>
      simp only [d306071, d349523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d306209 q = 1) (hb : d349583 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306209, d349583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306209, d349583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306212 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306213 q = 1) (hb : d349584 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306213, d349584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306213, d349584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306223 q = 1) (hb : d349585 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306223, d349585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306223, d349585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306224 q = 1) (hb : d349586 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306224, d349586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306224, d349586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306225 q = 1) (hb : d351235 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306225, d351235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306225, d351235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96257 (p : Pattern) (ha : d306265 p = 1) (hb : d351245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306254 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306107 q = 1) (hb : d349559 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306107, d349559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95899 q ha hb
    | true =>
      simp only [d306107, d349559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d306255 q = 1) (hb : d351241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306255, d351241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306255, d351241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306261 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306262 q = 1) (hb : d351242 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306262, d351242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306262, d351242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306263 q = 1) (hb : d351243 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306263, d351243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306263, d351243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306264 q = 1) (hb : d351244 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306264, d351244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306264, d351244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306265 q = 1) (hb : d351245 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306265, d351245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306265, d351245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96258 (p : Pattern) (ha : d306271 p = 1) (hb : d351251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306138 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306217 q = 1) (hb : d349588 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306217, d349588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96254 q ha hb
    | true =>
      simp only [d306217, d349588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96255 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306219 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306220 q = 1) (hb : d349589 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306220, d349589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306220, d349589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306221 q = 1) (hb : d351233 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306221, d351233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306221, d351233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306222 q = 1) (hb : d351234 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306222, d351234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306222, d351234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306226 q = 1) (hb : d351236 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306226, d351236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306226, d351236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96256 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d306227 q = 1) (hb : d351237 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306227, d351237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306227, d351237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d306228 q = 1) (hb : d351238 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306228, d351238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d306228, d351238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d306229 q = 1) (hb : d351239 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306229, d351239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306229, d351239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d306230 q = 1) (hb : d351240 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306230, d351240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306230, d351240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306266 q = 1) (hb : d351246 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306266, d351246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306266, d351246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96257 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306267 q = 1) (hb : d351247 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306267, d351247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306267, d351247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306268 q = 1) (hb : d351248 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306268, d351248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d306268, d351248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d306269 q = 1) (hb : d351249 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306269, d351249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d306269, d351249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d306270 q = 1) (hb : d351250 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306270, d351250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d306270, d351250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d306271 q = 1) (hb : d351251 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d306271, d351251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d306271, d351251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96259 (p : Pattern) (ha : d306277 p = 1) (hb : d351257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d306119 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d306119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d306119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80480 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d306120 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d306120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d306120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d306121 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d306121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d306121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d306122 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d306122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d306122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d306123 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d306123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d306123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306272 q = 1) (hb : d351252 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d306272, d351252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306272, d351252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96258 q ha hb
  have h8 (q : Pattern) (ha : d306273 q = 1) (hb : d351253 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d306273, d351253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306273, d351253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306274 q = 1) (hb : d351254 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d306274, d351254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306274, d351254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306275 q = 1) (hb : d351255 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d306275, d351255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306275, d351255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d306276 q = 1) (hb : d351256 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d306276, d351256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306276, d351256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d306277 q = 1) (hb : d351257 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d306277, d351257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d306277, d351257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro96260 (p : Pattern) (ha : d306394 p = 1) (hb : d349750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306330 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d306383 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306295 q = 1) (hb : d349745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306295, d349745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95930 q ha hb
    | true =>
      simp only [d306295, d349745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95931 q ha hb
  have h5 (q : Pattern) (ha : d306384 q = 1) (hb : d349746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306384, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d306384, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d306390 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d306391 q = 1) (hb : d349747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306391, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d306391, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306392 q = 1) (hb : d349748 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306392, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306392, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306393 q = 1) (hb : d349749 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306393, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306393, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306394 q = 1) (hb : d349750 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306394, d349750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306394, d349750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96261 (p : Pattern) (ha : d306415 p = 1) (hb : d349760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306321 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306330 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306295 q = 1) (hb : d349745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306295, d349745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95930 q ha hb
    | true =>
      simp only [d306295, d349745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95931 q ha hb
  have h4 (q : Pattern) (ha : d306384 q = 1) (hb : d349746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306384, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306384, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d306390 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306391 q = 1) (hb : d349747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306391, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306391, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d306392 q = 1) (hb : d349748 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306392, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306392, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306393 q = 1) (hb : d349749 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306393, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306393, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d306400 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306405 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d306407 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306305 q = 1) (hb : d349755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306305, d349755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95933 q ha hb
    | true =>
      simp only [d306305, d349755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95934 q ha hb
  have h13 (q : Pattern) (ha : d306408 q = 1) (hb : d349756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306408, d349756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d306408, d349756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306411 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306412 q = 1) (hb : d349757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306412, d349757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306412, d349757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306413 q = 1) (hb : d349758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306413, d349758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d306413, d349758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d306414 q = 1) (hb : d349759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306414, d349759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d306414, d349759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d306415 q = 1) (hb : d349760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306415, d349760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306415, d349760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96262 (p : Pattern) (ha : d306435 p = 1) (hb : d351260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306407 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306305 q = 1) (hb : d349755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306305, d349755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95933 q ha hb
    | true =>
      simp only [d306305, d349755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95934 q ha hb
  have h3 (q : Pattern) (ha : d306408 q = 1) (hb : d349756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306408, d349756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306408, d349756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306411 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306412 q = 1) (hb : d349757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306412, d349757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306412, d349757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306433 q = 1) (hb : d349758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306433, d349758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306433, d349758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306434 q = 1) (hb : d349759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306434, d349759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306434, d349759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306435 q = 1) (hb : d351260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306435, d351260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306435, d351260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96263 (p : Pattern) (ha : d306503 p = 1) (hb : d351271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306492 q = 1) (hb : d351266 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306492, d351266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95968 q ha hb
    | true =>
      simp only [d306492, d351266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95971 q ha hb
  have h3 (q : Pattern) (ha : d306493 q = 1) (hb : d351267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306493, d351267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306493, d351267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306499 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306500 q = 1) (hb : d351268 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306500, d351268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306500, d351268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306501 q = 1) (hb : d351269 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306501, d351269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306501, d351269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306502 q = 1) (hb : d351270 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306502, d351270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306502, d351270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306503 q = 1) (hb : d351271 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306503, d351271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306503, d351271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96264 (p : Pattern) (ha : d306516 p = 1) (hb : d351277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306416 q = 1) (hb : d349761 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306416, d349761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96260 q ha hb
    | true =>
      simp only [d306416, d349761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96261 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306429 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306430 q = 1) (hb : d349762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306430, d349762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306430, d349762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306431 q = 1) (hb : d351258 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306431, d351258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306431, d351258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306432 q = 1) (hb : d351259 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306432, d351259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306432, d351259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306436 q = 1) (hb : d351261 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306436, d351261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306436, d351261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96262 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d306438 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d306439 q = 1) (hb : d351262 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306439, d351262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306439, d351262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d306440 q = 1) (hb : d351263 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306440, d351263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d306440, d351263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d306441 q = 1) (hb : d351264 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306441, d351264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306441, d351264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d306442 q = 1) (hb : d351265 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306442, d351265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306442, d351265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306504 q = 1) (hb : d351272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306504, d351272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306504, d351272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96263 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306511 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306512 q = 1) (hb : d351273 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306512, d351273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306512, d351273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306513 q = 1) (hb : d351274 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306513, d351274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d306513, d351274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d306514 q = 1) (hb : d351275 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306514, d351275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d306514, d351275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d306515 q = 1) (hb : d351276 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306515, d351276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d306515, d351276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d306516 q = 1) (hb : d351277 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d306516, d351277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d306516, d351277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96265 (p : Pattern) (ha : d306522 p = 1) (hb : d351283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306517 q = 1) (hb : d351278 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d306517, d351278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306517, d351278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96264 q ha hb
  have h2 (q : Pattern) (ha : d306518 q = 1) (hb : d351279 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d306518, d351279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306518, d351279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306519 q = 1) (hb : d351280 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d306519, d351280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306519, d351280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306520 q = 1) (hb : d351281 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d306520, d351281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306520, d351281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306521 q = 1) (hb : d351282 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d306521, d351282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306521, d351282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306522 q = 1) (hb : d351283 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d306522, d351283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306522, d351283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96266 (p : Pattern) (ha : d306670 p = 1) (hb : d350007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306585 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d306659 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306559 q = 1) (hb : d350002 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306559, d350002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95981 q ha hb
    | true =>
      simp only [d306559, d350002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95982 q ha hb
  have h5 (q : Pattern) (ha : d306660 q = 1) (hb : d350003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306660, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d306660, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d306666 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d306667 q = 1) (hb : d350004 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306667, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d306667, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306668 q = 1) (hb : d350005 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306668, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306668, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306669 q = 1) (hb : d350006 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306669, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306669, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306670 q = 1) (hb : d350007 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306670, d350007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306670, d350007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96267 (p : Pattern) (ha : d306691 p = 1) (hb : d350017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306585 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306559 q = 1) (hb : d350002 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306559, d350002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95981 q ha hb
    | true =>
      simp only [d306559, d350002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95982 q ha hb
  have h4 (q : Pattern) (ha : d306660 q = 1) (hb : d350003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306660, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306660, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d306666 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306667 q = 1) (hb : d350004 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306667, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306667, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d306668 q = 1) (hb : d350005 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306668, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306668, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306669 q = 1) (hb : d350006 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306669, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306669, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d306676 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306681 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d306683 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306569 q = 1) (hb : d350012 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306569, d350012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95984 q ha hb
    | true =>
      simp only [d306569, d350012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95985 q ha hb
  have h13 (q : Pattern) (ha : d306684 q = 1) (hb : d350013 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306684, d350013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d306684, d350013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306687 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306688 q = 1) (hb : d350014 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306688, d350014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306688, d350014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306689 q = 1) (hb : d350015 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306689, d350015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d306689, d350015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d306690 q = 1) (hb : d350016 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306690, d350016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d306690, d350016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d306691 q = 1) (hb : d350017 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306691, d350017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306691, d350017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96268 (p : Pattern) (ha : d306711 p = 1) (hb : d351287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306683 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306569 q = 1) (hb : d350012 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306569, d350012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95984 q ha hb
    | true =>
      simp only [d306569, d350012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95985 q ha hb
  have h3 (q : Pattern) (ha : d306684 q = 1) (hb : d350013 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306684, d350013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306684, d350013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306687 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306688 q = 1) (hb : d350014 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306688, d350014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306688, d350014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306709 q = 1) (hb : d350015 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306709, d350015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306709, d350015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306710 q = 1) (hb : d350016 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306710, d350016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306710, d350016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306711 q = 1) (hb : d351287 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306711, d351287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306711, d351287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96269 (p : Pattern) (ha : d306796 p = 1) (hb : d351298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306780 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306785 q = 1) (hb : d351293 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306785, d351293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96023 q ha hb
    | true =>
      simp only [d306785, d351293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96026 q ha hb
  have h3 (q : Pattern) (ha : d306786 q = 1) (hb : d351294 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306786, d351294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306786, d351294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306792 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306793 q = 1) (hb : d351295 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306793, d351295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306793, d351295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306794 q = 1) (hb : d351296 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306794, d351296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306794, d351296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306795 q = 1) (hb : d351297 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306795, d351297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306795, d351297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306796 q = 1) (hb : d351298 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306796, d351298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306796, d351298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96270 (p : Pattern) (ha : d306809 p = 1) (hb : d351304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306692 q = 1) (hb : d350018 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306692, d350018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96266 q ha hb
    | true =>
      simp only [d306692, d350018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96267 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306706 q = 1) (hb : d350019 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306706, d350019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306706, d350019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306707 q = 1) (hb : d351285 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306707, d351285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306707, d351285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306708 q = 1) (hb : d351286 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306708, d351286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306708, d351286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306712 q = 1) (hb : d351288 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306712, d351288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306712, d351288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96268 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d306714 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d306715 q = 1) (hb : d351289 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306715, d351289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306715, d351289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d306716 q = 1) (hb : d351290 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306716, d351290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d306716, d351290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d306717 q = 1) (hb : d351291 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306717, d351291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306717, d351291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d306718 q = 1) (hb : d351292 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306718, d351292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306718, d351292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306797 q = 1) (hb : d351299 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306797, d351299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306797, d351299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96269 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306804 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306805 q = 1) (hb : d351300 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306805, d351300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306805, d351300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306806 q = 1) (hb : d351301 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306806, d351301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d306806, d351301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d306807 q = 1) (hb : d351302 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306807, d351302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d306807, d351302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d306808 q = 1) (hb : d351303 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306808, d351303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d306808, d351303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d306809 q = 1) (hb : d351304 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d306809, d351304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d306809, d351304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96271 (p : Pattern) (ha : d306815 p = 1) (hb : d351310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306810 q = 1) (hb : d351305 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d306810, d351305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306810, d351305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96270 q ha hb
  have h2 (q : Pattern) (ha : d306811 q = 1) (hb : d351306 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d306811, d351306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306811, d351306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306812 q = 1) (hb : d351307 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d306812, d351307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306812, d351307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306813 q = 1) (hb : d351308 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d306813, d351308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306813, d351308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306814 q = 1) (hb : d351309 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d306814, d351309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306814, d351309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306815 q = 1) (hb : d351310 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d306815, d351310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306815, d351310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96272 (p : Pattern) (ha : d307028 p = 1) (hb : d350312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306944 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307008 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306909 q = 1) (hb : d350307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306909, d350307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96042 q ha hb
    | true =>
      simp only [d306909, d350307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96043 q ha hb
  have h5 (q : Pattern) (ha : d307009 q = 1) (hb : d350308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307009, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307009, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d307024 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d307025 q = 1) (hb : d350309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307025, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307025, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d307026 q = 1) (hb : d350310 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307026, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307026, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307027 q = 1) (hb : d350311 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307027, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307027, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307028 q = 1) (hb : d350312 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307028, d350312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307028, d350312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96273 (p : Pattern) (ha : d307049 p = 1) (hb : d350322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306909 q = 1) (hb : d350307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306909, d350307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96042 q ha hb
    | true =>
      simp only [d306909, d350307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96043 q ha hb
  have h4 (q : Pattern) (ha : d307009 q = 1) (hb : d350308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307009, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307009, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307024 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d307025 q = 1) (hb : d350309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307025, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307025, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d307026 q = 1) (hb : d350310 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307026, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307026, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307027 q = 1) (hb : d350311 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307027, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307027, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307034 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307039 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307041 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306919 q = 1) (hb : d350317 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306919, d350317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96045 q ha hb
    | true =>
      simp only [d306919, d350317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96046 q ha hb
  have h13 (q : Pattern) (ha : d307042 q = 1) (hb : d350318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307042, d350318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d307042, d350318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307045 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307046 q = 1) (hb : d350319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307046, d350319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307046, d350319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307047 q = 1) (hb : d350320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307047, d350320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d307047, d350320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307048 q = 1) (hb : d350321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307048, d350321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d307048, d350321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307049 q = 1) (hb : d350322 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307049, d350322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307049, d350322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96274 (p : Pattern) (ha : d307069 p = 1) (hb : d351315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307041 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306919 q = 1) (hb : d350317 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306919, d350317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96045 q ha hb
    | true =>
      simp only [d306919, d350317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96046 q ha hb
  have h3 (q : Pattern) (ha : d307042 q = 1) (hb : d350318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307042, d350318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307042, d350318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307046 q = 1) (hb : d350319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307046, d350319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307046, d350319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307067 q = 1) (hb : d350320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307067, d350320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307067, d350320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307068 q = 1) (hb : d350321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307068, d350321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307068, d350321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307069 q = 1) (hb : d351315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307069, d351315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307069, d351315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96275 (p : Pattern) (ha : d307190 p = 1) (hb : d351326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307170 q = 1) (hb : d351321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307170, d351321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96085 q ha hb
    | true =>
      simp only [d307170, d351321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96090 q ha hb
  have h3 (q : Pattern) (ha : d307171 q = 1) (hb : d351322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307171, d351322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307171, d351322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307186 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307187 q = 1) (hb : d351323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307187, d351323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307187, d351323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307188 q = 1) (hb : d351324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307188, d351324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307188, d351324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307189 q = 1) (hb : d351325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307189, d351325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307189, d351325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307190 q = 1) (hb : d351326 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307190, d351326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307190, d351326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96276 (p : Pattern) (ha : d307203 p = 1) (hb : d351332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306927 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307050 q = 1) (hb : d350323 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307050, d350323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96272 q ha hb
    | true =>
      simp only [d307050, d350323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96273 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307064 q = 1) (hb : d350324 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307064, d350324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307064, d350324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307065 q = 1) (hb : d351313 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307065, d351313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307065, d351313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307066 q = 1) (hb : d351314 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307066, d351314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307066, d351314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307070 q = 1) (hb : d351316 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307070, d351316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307070, d351316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96274 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307072 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307073 q = 1) (hb : d351317 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307073, d351317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307073, d351317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307074 q = 1) (hb : d351318 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307074, d351318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307074, d351318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307075 q = 1) (hb : d351319 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307075, d351319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307075, d351319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307076 q = 1) (hb : d351320 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307076, d351320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307076, d351320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307191 q = 1) (hb : d351327 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307191, d351327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307191, d351327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96275 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307198 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307199 q = 1) (hb : d351328 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307199, d351328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307199, d351328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307200 q = 1) (hb : d351329 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307200, d351329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307200, d351329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307201 q = 1) (hb : d351330 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307201, d351330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307201, d351330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307202 q = 1) (hb : d351331 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307202, d351331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307202, d351331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307203 q = 1) (hb : d351332 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307203, d351332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307203, d351332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96277 (p : Pattern) (ha : d307209 p = 1) (hb : d351338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307204 q = 1) (hb : d351333 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307204, d351333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307204, d351333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96276 q ha hb
  have h2 (q : Pattern) (ha : d307205 q = 1) (hb : d351334 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307205, d351334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307205, d351334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307206 q = 1) (hb : d351335 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307206, d351335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307206, d351335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307207 q = 1) (hb : d351336 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307207, d351336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307207, d351336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307208 q = 1) (hb : d351337 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307208, d351337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307208, d351337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307209 q = 1) (hb : d351338 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307209, d351338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307209, d351338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96278 (p : Pattern) (ha : d307443 p = 1) (hb : d350669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307350 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307359 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307410 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d307324 q = 1) (hb : d350664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307324, d350664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96110 q ha hb
    | true =>
      simp only [d307324, d350664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96111 q ha hb
  have h5 (q : Pattern) (ha : d307411 q = 1) (hb : d350665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307411, d350665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307411, d350665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d307439 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d307440 q = 1) (hb : d350666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307440, d350666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307440, d350666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d307441 q = 1) (hb : d350667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307441, d350667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307441, d350667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307442 q = 1) (hb : d350668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307442, d350668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307442, d350668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307443 q = 1) (hb : d350669 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307443, d350669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307443, d350669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96279 (p : Pattern) (ha : d307464 p = 1) (hb : d350679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307350 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307410 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307324 q = 1) (hb : d350664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307324, d350664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96110 q ha hb
    | true =>
      simp only [d307324, d350664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96111 q ha hb
  have h4 (q : Pattern) (ha : d307411 q = 1) (hb : d350665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307411, d350665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307411, d350665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307439 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d307440 q = 1) (hb : d350666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307440, d350666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307440, d350666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d307441 q = 1) (hb : d350667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307441, d350667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307441, d350667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307442 q = 1) (hb : d350668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307442, d350668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307442, d350668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307449 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307454 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307456 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d307334 q = 1) (hb : d350674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307334, d350674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96113 q ha hb
    | true =>
      simp only [d307334, d350674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96114 q ha hb
  have h13 (q : Pattern) (ha : d307457 q = 1) (hb : d350675 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307457, d350675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d307457, d350675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307460 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307461 q = 1) (hb : d350676 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307461, d350676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307461, d350676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307462 q = 1) (hb : d350677 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307462, d350677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d307462, d350677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307463 q = 1) (hb : d350678 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307463, d350678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d307463, d350678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307464 q = 1) (hb : d350679 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307464, d350679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307464, d350679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96280 (p : Pattern) (ha : d307484 p = 1) (hb : d351344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307334 q = 1) (hb : d350674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307334, d350674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96113 q ha hb
    | true =>
      simp only [d307334, d350674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96114 q ha hb
  have h3 (q : Pattern) (ha : d307457 q = 1) (hb : d350675 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307457, d350675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307457, d350675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307461 q = 1) (hb : d350676 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307461, d350676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307461, d350676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307482 q = 1) (hb : d350677 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307482, d350677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307482, d350677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307483 q = 1) (hb : d350678 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307483, d350678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307483, d350678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307484 q = 1) (hb : d351344 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307484, d351344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307484, d351344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96281 (p : Pattern) (ha : d307616 p = 1) (hb : d351355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307580 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307585 q = 1) (hb : d351350 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307585, d351350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96155 q ha hb
    | true =>
      simp only [d307585, d351350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96161 q ha hb
  have h3 (q : Pattern) (ha : d307586 q = 1) (hb : d351351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307586, d351351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307586, d351351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307612 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307613 q = 1) (hb : d351352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307613, d351352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307613, d351352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307614 q = 1) (hb : d351353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307614, d351353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307614, d351353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307615 q = 1) (hb : d351354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307615, d351354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307615, d351354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307616 q = 1) (hb : d351355 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307616, d351355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307616, d351355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96282 (p : Pattern) (ha : d307629 p = 1) (hb : d351361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307342 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307465 q = 1) (hb : d350680 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307465, d350680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96278 q ha hb
    | true =>
      simp only [d307465, d350680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96279 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307479 q = 1) (hb : d350681 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307479, d350681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307479, d350681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307480 q = 1) (hb : d351342 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307480, d351342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307480, d351342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307481 q = 1) (hb : d351343 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307481, d351343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307481, d351343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307485 q = 1) (hb : d351345 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307485, d351345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307485, d351345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96280 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307487 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307488 q = 1) (hb : d351346 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307488, d351346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307488, d351346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307489 q = 1) (hb : d351347 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307489, d351347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307489, d351347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307490 q = 1) (hb : d351348 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307490, d351348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307490, d351348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307491 q = 1) (hb : d351349 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307491, d351349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307491, d351349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307617 q = 1) (hb : d351356 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307617, d351356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307617, d351356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96281 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307625 q = 1) (hb : d351357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307625, d351357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307625, d351357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307626 q = 1) (hb : d351358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307626, d351358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307626, d351358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307627 q = 1) (hb : d351359 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307627, d351359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307627, d351359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307628 q = 1) (hb : d351360 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307628, d351360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307628, d351360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307629 q = 1) (hb : d351361 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307629, d351361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307629, d351361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96283 (p : Pattern) (ha : d307635 p = 1) (hb : d351367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307630 q = 1) (hb : d351362 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307630, d351362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307630, d351362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96282 q ha hb
  have h2 (q : Pattern) (ha : d307631 q = 1) (hb : d351363 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307631, d351363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307631, d351363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307632 q = 1) (hb : d351364 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307632, d351364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307632, d351364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307633 q = 1) (hb : d351365 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307633, d351365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307633, d351365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307634 q = 1) (hb : d351366 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307634, d351366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307634, d351366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307635 q = 1) (hb : d351367 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307635, d351367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307635, d351367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96284 (p : Pattern) (ha : d307774 p = 1) (hb : d350988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307733 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d307698 q = 1) (hb : d350983 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307698, d350983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96171 q ha hb
    | true =>
      simp only [d307698, d350983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96172 q ha hb
  have h5 (q : Pattern) (ha : d307748 q = 1) (hb : d350984 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307748, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307748, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d307770 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d307771 q = 1) (hb : d350985 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307771, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307771, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d307772 q = 1) (hb : d350986 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307772, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307772, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307773 q = 1) (hb : d350987 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307773, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307773, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307774 q = 1) (hb : d350988 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307774, d350988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307774, d350988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96285 (p : Pattern) (ha : d307795 p = 1) (hb : d350998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307733 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307698 q = 1) (hb : d350983 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307698, d350983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96171 q ha hb
    | true =>
      simp only [d307698, d350983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96172 q ha hb
  have h4 (q : Pattern) (ha : d307748 q = 1) (hb : d350984 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307748, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307748, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307770 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d307771 q = 1) (hb : d350985 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307771, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307771, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d307772 q = 1) (hb : d350986 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307772, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307772, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307773 q = 1) (hb : d350987 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307773, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307773, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307780 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307785 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307787 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d307708 q = 1) (hb : d350993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307708, d350993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96174 q ha hb
    | true =>
      simp only [d307708, d350993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96175 q ha hb
  have h13 (q : Pattern) (ha : d307788 q = 1) (hb : d350994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307788, d350994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d307788, d350994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307791 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307792 q = 1) (hb : d350995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307792, d350995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307792, d350995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307793 q = 1) (hb : d350996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307793, d350996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d307793, d350996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307794 q = 1) (hb : d350997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307794, d350997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d307794, d350997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307795 q = 1) (hb : d350998 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307795, d350998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307795, d350998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96286 (p : Pattern) (ha : d307815 p = 1) (hb : d351374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307787 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307708 q = 1) (hb : d350993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307708, d350993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96174 q ha hb
    | true =>
      simp only [d307708, d350993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96175 q ha hb
  have h3 (q : Pattern) (ha : d307788 q = 1) (hb : d350994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307788, d350994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307788, d350994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307791 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307792 q = 1) (hb : d350995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307792, d350995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307792, d350995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307813 q = 1) (hb : d350996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307813, d350996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307813, d350996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307814 q = 1) (hb : d350997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307814, d350997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307814, d350997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307815 q = 1) (hb : d351374 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307815, d351374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307815, d351374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96287 (p : Pattern) (ha : d307906 p = 1) (hb : d351385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307875 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307880 q = 1) (hb : d351380 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307880, d351380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96205 q ha hb
    | true =>
      simp only [d307880, d351380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96210 q ha hb
  have h3 (q : Pattern) (ha : d307881 q = 1) (hb : d351381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307881, d351381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307881, d351381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307903 q = 1) (hb : d351382 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307903, d351382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307903, d351382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307904 q = 1) (hb : d351383 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307904, d351383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307904, d351383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307905 q = 1) (hb : d351384 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307905, d351384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307905, d351384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307906 q = 1) (hb : d351385 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307906, d351385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307906, d351385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96288 (p : Pattern) (ha : d307919 p = 1) (hb : d351391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307716 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307796 q = 1) (hb : d350999 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307796, d350999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96284 q ha hb
    | true =>
      simp only [d307796, d350999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96285 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307810 q = 1) (hb : d351000 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307810, d351000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307810, d351000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307811 q = 1) (hb : d351372 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307811, d351372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307811, d351372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307812 q = 1) (hb : d351373 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307812, d351373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307812, d351373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307816 q = 1) (hb : d351375 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307816, d351375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307816, d351375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96286 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307818 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307819 q = 1) (hb : d351376 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307819, d351376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307819, d351376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307820 q = 1) (hb : d351377 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307820, d351377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307820, d351377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307821 q = 1) (hb : d351378 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307821, d351378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307821, d351378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307822 q = 1) (hb : d351379 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307822, d351379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307822, d351379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307907 q = 1) (hb : d351386 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307907, d351386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307907, d351386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96287 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307914 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307915 q = 1) (hb : d351387 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307915, d351387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307915, d351387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307916 q = 1) (hb : d351388 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307916, d351388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307916, d351388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307917 q = 1) (hb : d351389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307917, d351389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307917, d351389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307918 q = 1) (hb : d351390 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307918, d351390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307918, d351390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307919 q = 1) (hb : d351391 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307919, d351391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307919, d351391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96289 (p : Pattern) (ha : d307925 p = 1) (hb : d351397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307920 q = 1) (hb : d351392 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307920, d351392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307920, d351392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96288 q ha hb
  have h2 (q : Pattern) (ha : d307921 q = 1) (hb : d351393 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307921, d351393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307921, d351393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307922 q = 1) (hb : d351394 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307922, d351394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307922, d351394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307923 q = 1) (hb : d351395 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307923, d351395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307923, d351395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307924 q = 1) (hb : d351396 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307924, d351396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307924, d351396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307925 q = 1) (hb : d351397 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307925, d351397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307925, d351397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96290 (p : Pattern) (ha : d307931 p = 1) (hb : d351403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d306523 q = 1) (hb : d351284 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306523, d351284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96259 q ha hb
    | true =>
      simp only [d306523, d351284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96265 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306816 q = 1) (hb : d351311 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306816, d351311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306816, d351311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96271 q ha hb
  have h3 (q : Pattern) (ha : d306817 q = 1) (hb : d351312 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d306817, d351312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d306817, d351312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307210 q = 1) (hb : d351339 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307210, d351339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307210, d351339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96277 q ha hb
  have h5 (q : Pattern) (ha : d307211 q = 1) (hb : d351340 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307211, d351340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307211, d351340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307212 q = 1) (hb : d351341 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307212, d351341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307212, d351341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307636 q = 1) (hb : d351368 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307636, d351368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307636, d351368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96283 q ha hb
  have h8 (q : Pattern) (ha : d307637 q = 1) (hb : d351369 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307637, d351369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307637, d351369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307638 q = 1) (hb : d351370 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307638, d351370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307638, d351370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307639 q = 1) (hb : d351371 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307639, d351371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307639, d351371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307926 q = 1) (hb : d351398 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307926, d351398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307926, d351398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96289 q ha hb
  have h12 (q : Pattern) (ha : d307927 q = 1) (hb : d351399 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307927, d351399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307927, d351399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307928 q = 1) (hb : d351400 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307928, d351400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307928, d351400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307929 q = 1) (hb : d351401 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307929, d351401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307929, d351401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307930 q = 1) (hb : d351402 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d307930, d351402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307930, d351402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307931 q = 1) (hb : d351403 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d307931, d351403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307931, d351403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro96291 (p : Pattern) (ha : d307937 p = 1) (hb : d351409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307932 q = 1) (hb : d351404 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d307932, d351404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96290 q ha hb
    | true =>
      simp only [d307932, d351404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307933 q = 1) (hb : d351405 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d307933, d351405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307933, d351405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307934 q = 1) (hb : d351406 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d307934, d351406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307934, d351406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307935 q = 1) (hb : d351407 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d307935, d351407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307935, d351407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307936 q = 1) (hb : d351408 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d307936, d351408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307936, d351408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307937 q = 1) (hb : d351409 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d307937, d351409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307937, d351409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96292 (p : Pattern) (ha : d307943 p = 1) (hb : d351415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307938 q = 1) (hb : d351410 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d307938, d351410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96291 q ha hb
    | true =>
      simp only [d307938, d351410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307939 q = 1) (hb : d351411 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d307939, d351411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307939, d351411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307940 q = 1) (hb : d351412 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d307940, d351412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307940, d351412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307941 q = 1) (hb : d351413 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d307941, d351413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307941, d351413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307942 q = 1) (hb : d351414 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d307942, d351414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307942, d351414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307943 q = 1) (hb : d351415 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d307943, d351415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307943, d351415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96293 (p : Pattern) (ha : d307949 p = 1) (hb : d351421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307944 q = 1) (hb : d351416 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d307944, d351416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96292 q ha hb
    | true =>
      simp only [d307944, d351416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307945 q = 1) (hb : d351417 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d307945, d351417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307945, d351417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307946 q = 1) (hb : d351418 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d307946, d351418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307946, d351418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307947 q = 1) (hb : d351419 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d307947, d351419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307947, d351419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307948 q = 1) (hb : d351420 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d307948, d351420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307948, d351420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307949 q = 1) (hb : d351421 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d307949, d351421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307949, d351421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96294 (p : Pattern) (ha : d307955 p = 1) (hb : d351427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307950 q = 1) (hb : d351422 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d307950, d351422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96293 q ha hb
    | true =>
      simp only [d307950, d351422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307951 q = 1) (hb : d351423 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d307951, d351423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307951, d351423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307952 q = 1) (hb : d351424 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d307952, d351424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307952, d351424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307953 q = 1) (hb : d351425 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d307953, d351425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307953, d351425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307954 q = 1) (hb : d351426 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d307954, d351426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307954, d351426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307955 q = 1) (hb : d351427 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d307955, d351427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307955, d351427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96295 (p : Pattern) (ha : d307961 p = 1) (hb : d351433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307956 q = 1) (hb : d351428 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d307956, d351428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96294 q ha hb
    | true =>
      simp only [d307956, d351428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307957 q = 1) (hb : d351429 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d307957, d351429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307957, d351429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307958 q = 1) (hb : d351430 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d307958, d351430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307958, d351430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307959 q = 1) (hb : d351431 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d307959, d351431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307959, d351431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307960 q = 1) (hb : d351432 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d307960, d351432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307960, d351432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307961 q = 1) (hb : d351433 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d307961, d351433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307961, d351433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96296 (p : Pattern) (ha : d307967 p = 1) (hb : d351439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307962 q = 1) (hb : d351434 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d307962, d351434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96295 q ha hb
    | true =>
      simp only [d307962, d351434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307963 q = 1) (hb : d351435 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d307963, d351435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307963, d351435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307964 q = 1) (hb : d351436 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d307964, d351436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307964, d351436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307965 q = 1) (hb : d351437 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d307965, d351437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307965, d351437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307966 q = 1) (hb : d351438 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d307966, d351438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307966, d351438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307967 q = 1) (hb : d351439 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d307967, d351439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307967, d351439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96297 (p : Pattern) (ha : d307973 p = 1) (hb : d351445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307968 q = 1) (hb : d351440 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d307968, d351440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96296 q ha hb
    | true =>
      simp only [d307968, d351440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307969 q = 1) (hb : d351441 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d307969, d351441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307969, d351441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307970 q = 1) (hb : d351442 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d307970, d351442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307970, d351442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307971 q = 1) (hb : d351443 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d307971, d351443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307971, d351443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307972 q = 1) (hb : d351444 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d307972, d351444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307972, d351444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307973 q = 1) (hb : d351445 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d307973, d351445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307973, d351445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96298 (p : Pattern) (ha : d309471 p = 1) (hb : d350988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44525 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44534 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44548 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d350983 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309467 q = 1) (hb : d350984 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309467, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309467, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44630 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309468 q = 1) (hb : d350985 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309468, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309468, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309469 q = 1) (hb : d350986 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309469, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309469, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309470 q = 1) (hb : d350987 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309470, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309470, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309471 q = 1) (hb : d350988 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309471, d350988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309471, d350988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96299 (p : Pattern) (ha : d309476 p = 1) (hb : d350998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44525 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44534 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44548 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d350983 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309467 q = 1) (hb : d350984 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309467, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309467, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44630 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309468 q = 1) (hb : d350985 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309468, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309468, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309469 q = 1) (hb : d350986 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309469, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309469, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309470 q = 1) (hb : d350987 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309470, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309470, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d44640 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d44645 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d44647 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d350993 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309472 q = 1) (hb : d350994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309472, d350994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309472, d350994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44654 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309473 q = 1) (hb : d350995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309473, d350995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309473, d350995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309474 q = 1) (hb : d350996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309474, d350996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309474, d350996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309475 q = 1) (hb : d350997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309475, d350997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309475, d350997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309476 q = 1) (hb : d350998 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309476, d350998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309476, d350998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96300 (p : Pattern) (ha : d309483 p = 1) (hb : d351374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44647 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d350993 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309472 q = 1) (hb : d350994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309472, d350994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309472, d350994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44654 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309473 q = 1) (hb : d350995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309473, d350995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309473, d350995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309481 q = 1) (hb : d350996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309481, d350996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309481, d350996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309482 q = 1) (hb : d350997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309482, d350997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309482, d350997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309483 q = 1) (hb : d351374 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309483, d351374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309483, d351374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96301 (p : Pattern) (ha : d309493 p = 1) (hb : d351385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44738 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d351380 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309489 q = 1) (hb : d351381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309489, d351381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309489, d351381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44804 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309490 q = 1) (hb : d351382 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309490, d351382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309490, d351382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309491 q = 1) (hb : d351383 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309491, d351383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309491, d351383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309492 q = 1) (hb : d351384 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309492, d351384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309492, d351384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309493 q = 1) (hb : d351385 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309493, d351385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309493, d351385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96302 (p : Pattern) (ha : d309499 p = 1) (hb : d351391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44517 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309477 q = 1) (hb : d350999 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309477, d350999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96298 q ha hb
    | true =>
      simp only [d309477, d350999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96299 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309478 q = 1) (hb : d351000 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309478, d351000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309478, d351000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309479 q = 1) (hb : d351372 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309479, d351372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309479, d351372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309480 q = 1) (hb : d351373 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309480, d351373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309480, d351373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309484 q = 1) (hb : d351375 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309484, d351375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309484, d351375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96300 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d44681 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309485 q = 1) (hb : d351376 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309485, d351376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309485, d351376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309486 q = 1) (hb : d351377 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309486, d351377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309486, d351377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309487 q = 1) (hb : d351378 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309487, d351378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309487, d351378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309488 q = 1) (hb : d351379 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309488, d351379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309488, d351379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309494 q = 1) (hb : d351386 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309494, d351386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309494, d351386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96301 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44820 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309495 q = 1) (hb : d351387 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309495, d351387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309495, d351387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309496 q = 1) (hb : d351388 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309496, d351388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309496, d351388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309497 q = 1) (hb : d351389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309497, d351389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309497, d351389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309498 q = 1) (hb : d351390 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309498, d351390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309498, d351390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309499 q = 1) (hb : d351391 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309499, d351391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309499, d351391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96303 (p : Pattern) (ha : d309505 p = 1) (hb : d351397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309500 q = 1) (hb : d351392 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309500, d351392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309500, d351392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96302 q ha hb
  have h2 (q : Pattern) (ha : d309501 q = 1) (hb : d351393 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309501, d351393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309501, d351393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309502 q = 1) (hb : d351394 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309502, d351394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309502, d351394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309503 q = 1) (hb : d351395 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309503, d351395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309503, d351395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309504 q = 1) (hb : d351396 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309504, d351396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309504, d351396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309505 q = 1) (hb : d351397 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309505, d351397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309505, d351397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96304 (p : Pattern) (ha : d309809 p = 1) (hb : d349580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42354 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42396 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d349516 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309805 q = 1) (hb : d349576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309805, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d42432 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309806 q = 1) (hb : d349577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309806, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309807 q = 1) (hb : d349578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309807, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309808 q = 1) (hb : d349579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309808, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309809 q = 1) (hb : d349580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309809, d349580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309809, d349580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96305 (p : Pattern) (ha : d309814 p = 1) (hb : d349587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42354 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42360 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d349516 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309805 q = 1) (hb : d349576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309805, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d42432 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309806 q = 1) (hb : d349577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309806, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309807 q = 1) (hb : d349578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309807, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309808 q = 1) (hb : d349579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309808, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d42441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42445 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d42447 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d349523 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309810 q = 1) (hb : d349583 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d349583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309810, d349583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42453 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309811 q = 1) (hb : d349584 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d349584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309811, d349584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309812 q = 1) (hb : d349585 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309812, d349585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309812, d349585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309813 q = 1) (hb : d349586 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309813, d349586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309813, d349586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309814 q = 1) (hb : d349587 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309814, d349587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309814, d349587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96306 (p : Pattern) (ha : d309821 p = 1) (hb : d351235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42447 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d349523 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309810 q = 1) (hb : d349583 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d349583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309810, d349583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42453 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309811 q = 1) (hb : d349584 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d349584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309811, d349584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309819 q = 1) (hb : d349585 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309819, d349585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309819, d349585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309820 q = 1) (hb : d349586 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309820, d349586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309820, d349586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309821 q = 1) (hb : d351235 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309821, d351235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309821, d351235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96307 (p : Pattern) (ha : d309831 p = 1) (hb : d351245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d349559 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309827 q = 1) (hb : d351241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309827, d351241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309827, d351241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42521 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309828 q = 1) (hb : d351242 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309828, d351242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309828, d351242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309829 q = 1) (hb : d351243 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309829, d351243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309829, d351243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309830 q = 1) (hb : d351244 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309830, d351244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309830, d351244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309831 q = 1) (hb : d351245 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309831, d351245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309831, d351245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96308 (p : Pattern) (ha : d309837 p = 1) (hb : d351251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42348 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309815 q = 1) (hb : d349588 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309815, d349588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96304 q ha hb
    | true =>
      simp only [d309815, d349588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96305 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42460 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309816 q = 1) (hb : d349589 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309816, d349589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309816, d349589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309817 q = 1) (hb : d351233 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309817, d351233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309817, d351233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309818 q = 1) (hb : d351234 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309818, d351234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309818, d351234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309822 q = 1) (hb : d351236 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309822, d351236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309822, d351236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96306 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309823 q = 1) (hb : d351237 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309823, d351237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309823, d351237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309824 q = 1) (hb : d351238 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309824, d351238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309824, d351238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309825 q = 1) (hb : d351239 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309825, d351239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309825, d351239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309826 q = 1) (hb : d351240 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309826, d351240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309826, d351240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309832 q = 1) (hb : d351246 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309832, d351246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309832, d351246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96307 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309833 q = 1) (hb : d351247 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309833, d351247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309833, d351247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309834 q = 1) (hb : d351248 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309834, d351248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309834, d351248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309835 q = 1) (hb : d351249 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309835, d351249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309835, d351249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309836 q = 1) (hb : d351250 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309836, d351250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309836, d351250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309837 q = 1) (hb : d351251 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309837, d351251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309837, d351251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96309 (p : Pattern) (ha : d309843 p = 1) (hb : d351257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d309800 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d309800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d309800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80535 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d309801 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d309801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d309801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d309802 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d309802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d309802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d309803 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d309803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d309803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d309804 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d309804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d309804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309838 q = 1) (hb : d351252 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309838, d351252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309838, d351252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96308 q ha hb
  have h8 (q : Pattern) (ha : d309839 q = 1) (hb : d351253 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309839, d351253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309839, d351253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309840 q = 1) (hb : d351254 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309840, d351254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309840, d351254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309841 q = 1) (hb : d351255 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309841, d351255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309841, d351255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309842 q = 1) (hb : d351256 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309842, d351256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309842, d351256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d309843 q = 1) (hb : d351257 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d351257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d309843, d351257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro96310 (p : Pattern) (ha : d309848 p = 1) (hb : d349750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42590 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42643 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d349745 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309844 q = 1) (hb : d349746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309844, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d42695 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309845 q = 1) (hb : d349747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309845, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309846 q = 1) (hb : d349748 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309846, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309847 q = 1) (hb : d349749 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309847, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309848 q = 1) (hb : d349750 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309848, d349750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309848, d349750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96311 (p : Pattern) (ha : d309853 p = 1) (hb : d349760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42590 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42643 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d349745 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309844 q = 1) (hb : d349746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309844, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d42695 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309845 q = 1) (hb : d349747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309845, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309846 q = 1) (hb : d349748 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309846, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309847 q = 1) (hb : d349749 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309847, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d42705 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42710 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d42712 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d349755 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309849 q = 1) (hb : d349756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d349756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309849, d349756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42719 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309850 q = 1) (hb : d349757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d349757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309850, d349757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309851 q = 1) (hb : d349758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309851, d349758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309851, d349758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309852 q = 1) (hb : d349759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309852, d349759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309852, d349759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309853 q = 1) (hb : d349760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309853, d349760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309853, d349760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96312 (p : Pattern) (ha : d309860 p = 1) (hb : d351260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42712 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d349755 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309849 q = 1) (hb : d349756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d349756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309849, d349756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42719 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309850 q = 1) (hb : d349757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d349757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309850, d349757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309858 q = 1) (hb : d349758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309858, d349758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309858, d349758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309859 q = 1) (hb : d349759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309859, d349759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309859, d349759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309860 q = 1) (hb : d351260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309860, d351260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309860, d351260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96313 (p : Pattern) (ha : d309870 p = 1) (hb : d351271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d351266 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309866 q = 1) (hb : d351267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309866, d351267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309866, d351267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42835 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309867 q = 1) (hb : d351268 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309867, d351268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309867, d351268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309868 q = 1) (hb : d351269 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309868, d351269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309868, d351269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309869 q = 1) (hb : d351270 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309869, d351270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309869, d351270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309870 q = 1) (hb : d351271 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309870, d351271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309870, d351271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96314 (p : Pattern) (ha : d309876 p = 1) (hb : d351277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309854 q = 1) (hb : d349761 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309854, d349761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96310 q ha hb
    | true =>
      simp only [d309854, d349761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96311 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42737 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309855 q = 1) (hb : d349762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309855, d349762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309855, d349762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309856 q = 1) (hb : d351258 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309856, d351258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309856, d351258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309857 q = 1) (hb : d351259 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309857, d351259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309857, d351259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309861 q = 1) (hb : d351261 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309861, d351261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309861, d351261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96312 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d42746 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309862 q = 1) (hb : d351262 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309862, d351262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309862, d351262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309863 q = 1) (hb : d351263 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309863, d351263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309863, d351263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309864 q = 1) (hb : d351264 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309864, d351264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309864, d351264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309865 q = 1) (hb : d351265 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309865, d351265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309865, d351265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309871 q = 1) (hb : d351272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309871, d351272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309871, d351272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96313 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42851 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309872 q = 1) (hb : d351273 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309872, d351273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309872, d351273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309873 q = 1) (hb : d351274 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309873, d351274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309873, d351274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309874 q = 1) (hb : d351275 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309874, d351275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309874, d351275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309875 q = 1) (hb : d351276 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309875, d351276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309875, d351276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309876 q = 1) (hb : d351277 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309876, d351277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309876, d351277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96315 (p : Pattern) (ha : d309882 p = 1) (hb : d351283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309877 q = 1) (hb : d351278 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309877, d351278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309877, d351278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96314 q ha hb
  have h2 (q : Pattern) (ha : d309878 q = 1) (hb : d351279 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309878, d351279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309878, d351279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309879 q = 1) (hb : d351280 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309879, d351280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309879, d351280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309880 q = 1) (hb : d351281 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309880, d351281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309880, d351281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309881 q = 1) (hb : d351282 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309881, d351282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309881, d351282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309882 q = 1) (hb : d351283 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309882, d351283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309882, d351283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96316 (p : Pattern) (ha : d309888 p = 1) (hb : d350007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42999 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d350002 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309884 q = 1) (hb : d350003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309884, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d43076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309885 q = 1) (hb : d350004 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309885, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309886 q = 1) (hb : d350005 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309886, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309887 q = 1) (hb : d350006 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309887, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309888 q = 1) (hb : d350007 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309888, d350007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309888, d350007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96317 (p : Pattern) (ha : d309893 p = 1) (hb : d350017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d350002 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309884 q = 1) (hb : d350003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309884, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d43076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309885 q = 1) (hb : d350004 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309885, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309886 q = 1) (hb : d350005 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309886, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309887 q = 1) (hb : d350006 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309887, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d43086 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d43091 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d43093 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d350012 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309889 q = 1) (hb : d350013 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d350013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309889, d350013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43100 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309890 q = 1) (hb : d350014 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d350014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309890, d350014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309891 q = 1) (hb : d350015 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309891, d350015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309891, d350015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309892 q = 1) (hb : d350016 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309892, d350016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309892, d350016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309893 q = 1) (hb : d350017 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309893, d350017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309893, d350017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96318 (p : Pattern) (ha : d309900 p = 1) (hb : d351287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d350012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309889 q = 1) (hb : d350013 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d350013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309889, d350013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43100 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309890 q = 1) (hb : d350014 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d350014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309890, d350014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309898 q = 1) (hb : d350015 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309898, d350015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309898, d350015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309899 q = 1) (hb : d350016 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309899, d350016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309899, d350016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309900 q = 1) (hb : d351287 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309900, d351287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309900, d351287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96319 (p : Pattern) (ha : d309910 p = 1) (hb : d351298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43193 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d351293 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309906 q = 1) (hb : d351294 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309906, d351294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309906, d351294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43248 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309907 q = 1) (hb : d351295 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309907, d351295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309907, d351295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309908 q = 1) (hb : d351296 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309908, d351296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309908, d351296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309909 q = 1) (hb : d351297 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309909, d351297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309909, d351297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309910 q = 1) (hb : d351298 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309910, d351298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309910, d351298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96320 (p : Pattern) (ha : d309916 p = 1) (hb : d351304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42917 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309894 q = 1) (hb : d350018 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309894, d350018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96316 q ha hb
    | true =>
      simp only [d309894, d350018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96317 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309895 q = 1) (hb : d350019 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309895, d350019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309895, d350019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309896 q = 1) (hb : d351285 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309896, d351285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309896, d351285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309897 q = 1) (hb : d351286 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309897, d351286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309897, d351286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309901 q = 1) (hb : d351288 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309901, d351288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309901, d351288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96318 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d43127 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309902 q = 1) (hb : d351289 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309902, d351289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309902, d351289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309903 q = 1) (hb : d351290 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309903, d351290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309903, d351290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309904 q = 1) (hb : d351291 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309904, d351291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309904, d351291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309905 q = 1) (hb : d351292 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309905, d351292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309905, d351292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309911 q = 1) (hb : d351299 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309911, d351299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309911, d351299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96319 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43264 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309912 q = 1) (hb : d351300 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309912, d351300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309912, d351300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309913 q = 1) (hb : d351301 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309913, d351301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309913, d351301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309914 q = 1) (hb : d351302 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309914, d351302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309914, d351302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309915 q = 1) (hb : d351303 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309915, d351303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309915, d351303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309916 q = 1) (hb : d351304 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309916, d351304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309916, d351304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96321 (p : Pattern) (ha : d309922 p = 1) (hb : d351310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309917 q = 1) (hb : d351305 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309917, d351305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309917, d351305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96320 q ha hb
  have h2 (q : Pattern) (ha : d309918 q = 1) (hb : d351306 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309918, d351306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309918, d351306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309919 q = 1) (hb : d351307 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309919, d351307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309919, d351307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309920 q = 1) (hb : d351308 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309920, d351308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309920, d351308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309921 q = 1) (hb : d351309 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309921, d351309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309921, d351309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309922 q = 1) (hb : d351310 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309922, d351310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309922, d351310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96322 (p : Pattern) (ha : d309929 p = 1) (hb : d350312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43468 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d350307 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309925 q = 1) (hb : d350308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309925, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309925, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d43595 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309926 q = 1) (hb : d350309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309926, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309926, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309927 q = 1) (hb : d350310 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309927, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309927, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309928 q = 1) (hb : d350311 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309928, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309928, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309929 q = 1) (hb : d350312 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309929, d350312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309929, d350312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96323 (p : Pattern) (ha : d309934 p = 1) (hb : d350322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43404 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43468 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d350307 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309925 q = 1) (hb : d350308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309925, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309925, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d43595 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309926 q = 1) (hb : d350309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309926, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309926, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309927 q = 1) (hb : d350310 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309927, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309927, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309928 q = 1) (hb : d350311 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309928, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309928, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d43605 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d43610 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d43612 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d350317 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309930 q = 1) (hb : d350318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309930, d350318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309930, d350318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43619 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309931 q = 1) (hb : d350319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309931, d350319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309931, d350319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309932 q = 1) (hb : d350320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309932, d350320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309932, d350320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309933 q = 1) (hb : d350321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309933, d350321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309933, d350321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309934 q = 1) (hb : d350322 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309934, d350322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309934, d350322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96324 (p : Pattern) (ha : d309941 p = 1) (hb : d351315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43612 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d350317 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309930 q = 1) (hb : d350318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309930, d350318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309930, d350318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43619 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309931 q = 1) (hb : d350319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309931, d350319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309931, d350319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309939 q = 1) (hb : d350320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309939, d350320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309939, d350320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309940 q = 1) (hb : d350321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309940, d350321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309940, d350321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309941 q = 1) (hb : d351315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309941, d351315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309941, d351315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96325 (p : Pattern) (ha : d309951 p = 1) (hb : d351326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d351321 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309947 q = 1) (hb : d351322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309947, d351322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309947, d351322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43812 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309948 q = 1) (hb : d351323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309948, d351323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309948, d351323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309949 q = 1) (hb : d351324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309949, d351324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309949, d351324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309950 q = 1) (hb : d351325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309950, d351325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309950, d351325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309951 q = 1) (hb : d351326 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309951, d351326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309951, d351326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96326 (p : Pattern) (ha : d309957 p = 1) (hb : d351332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309935 q = 1) (hb : d350323 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309935, d350323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96322 q ha hb
    | true =>
      simp only [d309935, d350323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96323 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309936 q = 1) (hb : d350324 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309936, d350324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309936, d350324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309937 q = 1) (hb : d351313 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309937, d351313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309937, d351313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309938 q = 1) (hb : d351314 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309938, d351314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309938, d351314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309942 q = 1) (hb : d351316 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309942, d351316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309942, d351316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96324 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d43646 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309943 q = 1) (hb : d351317 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309943, d351317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309943, d351317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309944 q = 1) (hb : d351318 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309944, d351318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309944, d351318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309945 q = 1) (hb : d351319 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309945, d351319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309945, d351319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309946 q = 1) (hb : d351320 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309946, d351320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309946, d351320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309952 q = 1) (hb : d351327 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309952, d351327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309952, d351327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96325 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43828 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309953 q = 1) (hb : d351328 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309953, d351328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309953, d351328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309954 q = 1) (hb : d351329 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309954, d351329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309954, d351329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309955 q = 1) (hb : d351330 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309955, d351330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309955, d351330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309956 q = 1) (hb : d351331 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309956, d351331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309956, d351331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309957 q = 1) (hb : d351332 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309957, d351332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309957, d351332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96327 (p : Pattern) (ha : d309963 p = 1) (hb : d351338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309958 q = 1) (hb : d351333 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309958, d351333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309958, d351333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96326 q ha hb
  have h2 (q : Pattern) (ha : d309959 q = 1) (hb : d351334 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309959, d351334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309959, d351334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309960 q = 1) (hb : d351335 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309960, d351335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309960, d351335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309961 q = 1) (hb : d351336 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309961, d351336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309961, d351336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309962 q = 1) (hb : d351337 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309962, d351337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309962, d351337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309963 q = 1) (hb : d351338 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309963, d351338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309963, d351338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96328 (p : Pattern) (ha : d309971 p = 1) (hb : d350669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43989 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44040 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d350664 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309967 q = 1) (hb : d350665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309967, d350665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309967, d350665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44181 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309968 q = 1) (hb : d350666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309968, d350666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309968, d350666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309969 q = 1) (hb : d350667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309969, d350667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309969, d350667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309970 q = 1) (hb : d350668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309970, d350668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309970, d350668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309971 q = 1) (hb : d350669 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309971, d350669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309971, d350669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96329 (p : Pattern) (ha : d309976 p = 1) (hb : d350679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44040 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d350664 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309967 q = 1) (hb : d350665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309967, d350665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309967, d350665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44181 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309968 q = 1) (hb : d350666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309968, d350666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309968, d350666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309969 q = 1) (hb : d350667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309969, d350667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309969, d350667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309970 q = 1) (hb : d350668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309970, d350668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309970, d350668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d44191 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d44196 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d44198 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d350674 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309972 q = 1) (hb : d350675 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309972, d350675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309972, d350675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44205 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309973 q = 1) (hb : d350676 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309973, d350676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309973, d350676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309974 q = 1) (hb : d350677 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309974, d350677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309974, d350677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309975 q = 1) (hb : d350678 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309975, d350678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309975, d350678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309976 q = 1) (hb : d350679 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309976, d350679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309976, d350679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96330 (p : Pattern) (ha : d309983 p = 1) (hb : d351344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d350674 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309972 q = 1) (hb : d350675 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309972, d350675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309972, d350675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44205 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309973 q = 1) (hb : d350676 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309973, d350676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309973, d350676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309981 q = 1) (hb : d350677 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309981, d350677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309981, d350677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309982 q = 1) (hb : d350678 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309982, d350678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309982, d350678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309983 q = 1) (hb : d351344 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309983, d351344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309983, d351344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96331 (p : Pattern) (ha : d309993 p = 1) (hb : d351355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d351350 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309989 q = 1) (hb : d351351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309989, d351351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309989, d351351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44409 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309990 q = 1) (hb : d351352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309990, d351352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309990, d351352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309991 q = 1) (hb : d351353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309991, d351353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309991, d351353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309992 q = 1) (hb : d351354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309992, d351354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309992, d351354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309993 q = 1) (hb : d351355 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309993, d351355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309993, d351355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96332 (p : Pattern) (ha : d309999 p = 1) (hb : d351361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309977 q = 1) (hb : d350680 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309977, d350680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96328 q ha hb
    | true =>
      simp only [d309977, d350680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96329 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44223 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309978 q = 1) (hb : d350681 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309978, d350681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309978, d350681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309979 q = 1) (hb : d351342 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309979, d351342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309979, d351342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309980 q = 1) (hb : d351343 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309980, d351343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309980, d351343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309984 q = 1) (hb : d351345 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309984, d351345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309984, d351345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96330 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d44232 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309985 q = 1) (hb : d351346 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309985, d351346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309985, d351346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309986 q = 1) (hb : d351347 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309986, d351347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309986, d351347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309987 q = 1) (hb : d351348 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309987, d351348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309987, d351348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309988 q = 1) (hb : d351349 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309988, d351349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309988, d351349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309994 q = 1) (hb : d351356 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309994, d351356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309994, d351356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96331 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44425 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309995 q = 1) (hb : d351357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309995, d351357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309995, d351357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309996 q = 1) (hb : d351358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309996, d351358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309996, d351358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309997 q = 1) (hb : d351359 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309997, d351359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309997, d351359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309998 q = 1) (hb : d351360 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309998, d351360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309998, d351360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309999 q = 1) (hb : d351361 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309999, d351361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309999, d351361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96333 (p : Pattern) (ha : d310005 p = 1) (hb : d351367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310000 q = 1) (hb : d351362 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d310000, d351362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310000, d351362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96332 q ha hb
  have h2 (q : Pattern) (ha : d310001 q = 1) (hb : d351363 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d310001, d351363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310001, d351363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310002 q = 1) (hb : d351364 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d310002, d351364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310002, d351364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310003 q = 1) (hb : d351365 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d310003, d351365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310003, d351365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310004 q = 1) (hb : d351366 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d310004, d351366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310004, d351366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310005 q = 1) (hb : d351367 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d310005, d351367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310005, d351367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96334 (p : Pattern) (ha : d310011 p = 1) (hb : d351403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d309883 q = 1) (hb : d351284 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309883, d351284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96309 q ha hb
    | true =>
      simp only [d309883, d351284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96315 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d309923 q = 1) (hb : d351311 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309923, d351311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309923, d351311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96321 q ha hb
  have h3 (q : Pattern) (ha : d309924 q = 1) (hb : d351312 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309924, d351312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309924, d351312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309964 q = 1) (hb : d351339 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309964, d351339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309964, d351339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96327 q ha hb
  have h5 (q : Pattern) (ha : d309965 q = 1) (hb : d351340 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309965, d351340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309965, d351340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309966 q = 1) (hb : d351341 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d351341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309966, d351341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d310006 q = 1) (hb : d351368 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d310006, d351368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310006, d351368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96333 q ha hb
  have h8 (q : Pattern) (ha : d310007 q = 1) (hb : d351369 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d310007, d351369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310007, d351369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d310008 q = 1) (hb : d351370 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d310008, d351370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310008, d351370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310009 q = 1) (hb : d351371 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d351371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d310009, d351371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309506 q = 1) (hb : d351398 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309506, d351398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309506, d351398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96303 q ha hb
  have h12 (q : Pattern) (ha : d309507 q = 1) (hb : d351399 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309507, d351399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309507, d351399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309508 q = 1) (hb : d351400 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309508, d351400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309508, d351400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309509 q = 1) (hb : d351401 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d309509, d351401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309509, d351401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d310010 q = 1) (hb : d351402 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d351402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d310010, d351402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d310011 q = 1) (hb : d351403 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, d351403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d310011, d351403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro96335 (p : Pattern) (ha : d310017 p = 1) (hb : d351409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d351404 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, d351404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96334 q ha hb
    | true =>
      simp only [d310012, d351404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d351405 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d351405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d351405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310014 q = 1) (hb : d351406 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d351406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d351406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310015 q = 1) (hb : d351407 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d351407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310015, d351407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310016 q = 1) (hb : d351408 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d351408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310016, d351408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310017 q = 1) (hb : d351409 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d351409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310017, d351409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96336 (p : Pattern) (ha : d310023 p = 1) (hb : d351415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d351410 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d351410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96335 q ha hb
    | true =>
      simp only [d310018, d351410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d351411 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d351411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d351411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310020 q = 1) (hb : d351412 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d351412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d351412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310021 q = 1) (hb : d351413 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d351413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310021, d351413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310022 q = 1) (hb : d351414 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d351414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310022, d351414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310023 q = 1) (hb : d351415 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, d351415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310023, d351415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96337 (p : Pattern) (ha : d310029 p = 1) (hb : d351421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d351416 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, d351416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96336 q ha hb
    | true =>
      simp only [d310024, d351416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d351417 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, d351417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, d351417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d351418 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, d351418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, d351418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d351419 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, d351419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, d351419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d351420 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, d351420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, d351420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d351421 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, d351421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, d351421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96338 (p : Pattern) (ha : d310035 p = 1) (hb : d351427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d351422 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, d351422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96337 q ha hb
    | true =>
      simp only [d310030, d351422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d351423 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, d351423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, d351423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d351424 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, d351424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, d351424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d351425 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, d351425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, d351425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d351426 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, d351426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, d351426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d351427 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, d351427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, d351427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96339 (p : Pattern) (ha : d310041 p = 1) (hb : d351433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d351428 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, d351428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96338 q ha hb
    | true =>
      simp only [d310036, d351428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d351429 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, d351429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, d351429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d351430 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, d351430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, d351430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d351431 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, d351431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, d351431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d351432 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, d351432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, d351432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d351433 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, d351433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, d351433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96340 (p : Pattern) (ha : d310047 p = 1) (hb : d351439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d351434 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, d351434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96339 q ha hb
    | true =>
      simp only [d310042, d351434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d351435 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, d351435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, d351435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d351436 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, d351436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, d351436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d351437 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, d351437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, d351437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d351438 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, d351438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, d351438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d351439 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, d351439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, d351439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96341 (p : Pattern) (ha : d310053 p = 1) (hb : d351445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d351440 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, d351440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96340 q ha hb
    | true =>
      simp only [d310048, d351440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d351441 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, d351441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, d351441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d351442 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, d351442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, d351442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d351443 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, d351443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, d351443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d351444 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, d351444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, d351444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d351445 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, d351445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, d351445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96342 (p : Pattern) (ha : d2000 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1997 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1998 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1999 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2000 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96343 (p : Pattern) (ha : d2015 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1997 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1998 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1999 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2013 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2014 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2015 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96344 (p : Pattern) (ha : d30087 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96342 q ha hb
    | true =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30079 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30080 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30081 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30082 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96343 q ha hb
    | true =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30083 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30084 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30085 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30086 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30087 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96345 (p : Pattern) (ha : d2039 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1997 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1998 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2013 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2014 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2027 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2039 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96346 (p : Pattern) (ha : d30097 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96342 q ha hb
    | true =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30082 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96343 q ha hb
    | true =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30083 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30084 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30085 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30086 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30092 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96345 q ha hb
    | true =>
      simp only [d30092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30093 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30094 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30095 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30096 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30097 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro96347 (p : Pattern) (ha : d2040 p = 1) (hb : d46864 p = 1) : d276849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1997 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2016 q = 1) (hb : d46864 q = 1) : d46864 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d2017 q = 1) (hb : d46864 q = 1) : d276820 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2017, d276820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2017, d276820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2018 q = 1) (hb : d46864 q = 1) : d276821 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2018, d276821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2018, d276821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2040 q = 1) (hb : d46864 q = 1) : d276849 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2040, d276849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2040, d276849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro96348 (p : Pattern) (ha : d2042 p = 1) (hb : d46864 p = 1) : d46867 p = 1 := by
  have h0 (q : Pattern) (ha : d2016 q = 1) (hb : d46864 q = 1) : d46864 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2021 q = 1) (hb : d46864 q = 1) : d46865 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2021, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2021, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2022 q = 1) (hb : d46864 q = 1) : d46866 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2022, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2022, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2042 q = 1) (hb : d46864 q = 1) : d46867 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2042, d46867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2042, d46867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h4 p ha hb
theorem andIntro96349 (p : Pattern) (ha : d2046 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1997 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2013 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2027 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d2046 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro96350 (p : Pattern) (ha : d39704 p = 1) (hb : d46864 p = 1) : d356652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96343 q ha hb
    | true =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30092 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96345 q ha hb
    | true =>
      simp only [d30092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30093 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30094 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30095 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30096 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2058 q = 1) (hb : d46864 q = 1) : d276850 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d276850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2058, d276850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96347 q ha hb
  have h9 (q : Pattern) (ha : d2043 q = 1) (hb : d46864 q = 1) : d46868 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2043, d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96348 q ha hb
  have h10 (q : Pattern) (ha : d2059 q = 1) (hb : d46864 q = 1) : d356646 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d356646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2059, d356646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2047 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96349 q ha hb
    | true =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2048 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2060 q = 1) (hb : d46864 q = 1) : d356647 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2060, d356647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2060, d356647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10405 q = 1) (hb : d46864 q = 1) : d276872 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d276872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96347 q ha hb
    | true =>
      simp only [d10405, d276872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10406 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96348 q ha hb
    | true =>
      simp only [d10406, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10407 q = 1) (hb : d46864 q = 1) : d356648 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d356648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10407, d356648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10408 q = 1) (hb : d46864 q = 1) : d356649 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d356649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10408, d356649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d32713 q = 1) (hb : d46864 q = 1) : d356650 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32713, d356650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32713, d356650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d32714 q = 1) (hb : d46864 q = 1) : d356651 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32714, d356651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d32714, d356651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d39704 q = 1) (hb : d46864 q = 1) : d356652 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39704, d356652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39704, d356652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro96351 (p : Pattern) (ha : d39710 p = 1) (hb : d46864 p = 1) : d356658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30088 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96344 q ha hb
    | true =>
      simp only [d30088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30089 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30090 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30091 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30098 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96346 q ha hb
    | true =>
      simp only [d30098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30099 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30100 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30101 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30102 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39705 q = 1) (hb : d46864 q = 1) : d356653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96350 q ha hb
    | true =>
      simp only [d39705, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39706 q = 1) (hb : d46864 q = 1) : d356654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39706, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d39707 q = 1) (hb : d46864 q = 1) : d356655 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39707, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39707, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39708 q = 1) (hb : d46864 q = 1) : d356656 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39708, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39708, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d39709 q = 1) (hb : d46864 q = 1) : d356657 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39709, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39709, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d39710 q = 1) (hb : d46864 q = 1) : d356658 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39710, d356658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39710, d356658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96352 (p : Pattern) (ha : d39716 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96342 q ha hb
    | true =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30082 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96343 q ha hb
    | true =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30083 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30084 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30085 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30086 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39711 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d39711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96345 q ha hb
    | true =>
      simp only [d39711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96349 q ha hb
  have h9 (q : Pattern) (ha : d39712 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d39712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d39713 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d39713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2047 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96349 q ha hb
    | true =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2048 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30103 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39714 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d39714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d39715 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d39715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d39715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d39716 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro96353 (p : Pattern) (ha : d39721 p = 1) (hb : d46864 p = 1) : d356652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96343 q ha hb
    | true =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39711 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d39711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96345 q ha hb
    | true =>
      simp only [d39711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96349 q ha hb
  have h4 (q : Pattern) (ha : d39712 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d39712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39713 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d39713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2047 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96349 q ha hb
    | true =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2048 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30103 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d39714 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d39714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39715 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d39715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2058 q = 1) (hb : d46864 q = 1) : d276850 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d276850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2058, d276850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96347 q ha hb
  have h12 (q : Pattern) (ha : d2043 q = 1) (hb : d46864 q = 1) : d46868 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2043, d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96348 q ha hb
  have h13 (q : Pattern) (ha : d2059 q = 1) (hb : d46864 q = 1) : d356646 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d356646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2059, d356646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2060 q = 1) (hb : d46864 q = 1) : d356647 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2060, d356647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2060, d356647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d10405 q = 1) (hb : d46864 q = 1) : d276872 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d276872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96347 q ha hb
    | true =>
      simp only [d10405, d276872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10406 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96348 q ha hb
    | true =>
      simp only [d10406, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d10407 q = 1) (hb : d46864 q = 1) : d356648 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d356648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10407, d356648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10408 q = 1) (hb : d46864 q = 1) : d356649 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d356649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10408, d356649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d32713 q = 1) (hb : d46864 q = 1) : d356650 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32713, d356650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32713, d356650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d32714 q = 1) (hb : d46864 q = 1) : d356651 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32714, d356651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32714, d356651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d39721 q = 1) (hb : d46864 q = 1) : d356652 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39721, d356652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39721, d356652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro96354 (p : Pattern) (ha : d39728 p = 1) (hb : d46864 p = 1) : d356660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39717 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96352 q ha hb
    | true =>
      simp only [d39717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39718 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39719 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39720 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39722 q = 1) (hb : d46864 q = 1) : d356653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96353 q ha hb
    | true =>
      simp only [d39722, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39723 q = 1) (hb : d46864 q = 1) : d356654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39723, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39724 q = 1) (hb : d46864 q = 1) : d356655 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39724, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39724, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39725 q = 1) (hb : d46864 q = 1) : d356656 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39725, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39725, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39726 q = 1) (hb : d46864 q = 1) : d356657 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39726, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39726, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39705 q = 1) (hb : d46864 q = 1) : d356653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96350 q ha hb
    | true =>
      simp only [d39705, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39706 q = 1) (hb : d46864 q = 1) : d356654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39706, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d39707 q = 1) (hb : d46864 q = 1) : d356655 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39707, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39707, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39708 q = 1) (hb : d46864 q = 1) : d356656 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39708, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39708, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d39727 q = 1) (hb : d46864 q = 1) : d356659 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39727, d356659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39727, d356659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39728 q = 1) (hb : d46864 q = 1) : d356660 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39728, d356660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39728, d356660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96355 (p : Pattern) (ha : d10411 p = 1) (hb : d46864 p = 1) : d356664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2058 q = 1) (hb : d46864 q = 1) : d276850 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d276850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2058, d276850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96347 q ha hb
  have h2 (q : Pattern) (ha : d2043 q = 1) (hb : d46864 q = 1) : d46868 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2043, d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96348 q ha hb
  have h3 (q : Pattern) (ha : d2059 q = 1) (hb : d46864 q = 1) : d356646 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d356646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2059, d356646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2076 q = 1) (hb : d46864 q = 1) : d356647 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, d356647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2076, d356647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10405 q = 1) (hb : d46864 q = 1) : d276872 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d276872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96347 q ha hb
    | true =>
      simp only [d10405, d276872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10406 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96348 q ha hb
    | true =>
      simp only [d10406, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10407 q = 1) (hb : d46864 q = 1) : d356648 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d356648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10407, d356648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10408 q = 1) (hb : d46864 q = 1) : d356649 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d356649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10408, d356649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10409 q = 1) (hb : d46864 q = 1) : d356650 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10409, d356650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10409, d356650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10410 q = 1) (hb : d46864 q = 1) : d356651 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10410, d356651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10410, d356651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10411 q = 1) (hb : d46864 q = 1) : d356664 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10411, d356664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10411, d356664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro96356 (p : Pattern) (ha : d39733 p = 1) (hb : d46864 p = 1) : d356670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39722 q = 1) (hb : d46864 q = 1) : d356653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96353 q ha hb
    | true =>
      simp only [d39722, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39723 q = 1) (hb : d46864 q = 1) : d356654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39723, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39724 q = 1) (hb : d46864 q = 1) : d356655 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39724, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39724, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39725 q = 1) (hb : d46864 q = 1) : d356656 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39725, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39725, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39732 q = 1) (hb : d46864 q = 1) : d356659 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39732, d356659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39732, d356659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10412 q = 1) (hb : d46864 q = 1) : d356665 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d356665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96355 q ha hb
    | true =>
      simp only [d10412, d356665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10414 q = 1) (hb : d46864 q = 1) : d356666 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d356666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10414, d356666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15555 q = 1) (hb : d46864 q = 1) : d356667 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d356667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, d356667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15556 q = 1) (hb : d46864 q = 1) : d356668 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d356668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15556, d356668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15557 q = 1) (hb : d46864 q = 1) : d356669 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d356669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15557, d356669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39733 q = 1) (hb : d46864 q = 1) : d356670 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39733, d356670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39733, d356670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96357 (p : Pattern) (ha : d39740 p = 1) (hb : d46864 p = 1) : d356677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39729 q = 1) (hb : d46864 q = 1) : d356661 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39729, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96351 q ha hb
    | true =>
      simp only [d39729, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96354 q ha hb
  have h2 (q : Pattern) (ha : d39730 q = 1) (hb : d46864 q = 1) : d356662 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39730, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39730, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39731 q = 1) (hb : d46864 q = 1) : d356663 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39731, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39731, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39734 q = 1) (hb : d46864 q = 1) : d356671 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39734, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96354 q ha hb
    | true =>
      simp only [d39734, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96356 q ha hb
  have h5 (q : Pattern) (ha : d39735 q = 1) (hb : d46864 q = 1) : d356672 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39735, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39735, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39736 q = 1) (hb : d46864 q = 1) : d356673 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39736, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39736, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39737 q = 1) (hb : d46864 q = 1) : d356674 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39737, d356674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39737, d356674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39738 q = 1) (hb : d46864 q = 1) : d356675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39738, d356675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39738, d356675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39739 q = 1) (hb : d46864 q = 1) : d356676 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39739, d356676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39739, d356676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39740 q = 1) (hb : d46864 q = 1) : d356677 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39740, d356677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39740, d356677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro96358 (p : Pattern) (ha : d39744 p = 1) (hb : d46864 p = 1) : d356681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39734 q = 1) (hb : d46864 q = 1) : d356671 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39734, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96354 q ha hb
    | true =>
      simp only [d39734, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96356 q ha hb
  have h2 (q : Pattern) (ha : d39735 q = 1) (hb : d46864 q = 1) : d356672 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39735, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39735, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39736 q = 1) (hb : d46864 q = 1) : d356673 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39736, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39736, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39738 q = 1) (hb : d46864 q = 1) : d356675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39738, d356675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39738, d356675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39743 q = 1) (hb : d46864 q = 1) : d356680 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39743, d356680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39743, d356680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39744 q = 1) (hb : d46864 q = 1) : d356681 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39744, d356681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39744, d356681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96359 (p : Pattern) (ha : d39750 p = 1) (hb : d46864 p = 1) : d356687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d46864 q = 1) : d356678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96357 q ha hb
    | true =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d46864 q = 1) : d356679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d46864 q = 1) : d356682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96358 q ha hb
    | true =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d46864 q = 1) : d356683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d46864 q = 1) : d356684 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39748 q = 1) (hb : d46864 q = 1) : d356685 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39748, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39748, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39749 q = 1) (hb : d46864 q = 1) : d356686 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39749, d356686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39749, d356686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39750 q = 1) (hb : d46864 q = 1) : d356687 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39750, d356687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39750, d356687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96360 (p : Pattern) (ha : d39754 p = 1) (hb : d46864 p = 1) : d356691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d46864 q = 1) : d356682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96358 q ha hb
    | true =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d46864 q = 1) : d356683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d46864 q = 1) : d356688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39752 q = 1) (hb : d46864 q = 1) : d356689 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39752, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39752, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39753 q = 1) (hb : d46864 q = 1) : d356690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39753, d356690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39753, d356690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39754 q = 1) (hb : d46864 q = 1) : d356691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39754, d356691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39754, d356691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96361 (p : Pattern) (ha : d39760 p = 1) (hb : d46864 p = 1) : d356697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39755 q = 1) (hb : d46864 q = 1) : d356692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39755, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96359 q ha hb
    | true =>
      simp only [d39755, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96360 q ha hb
  have h2 (q : Pattern) (ha : d39756 q = 1) (hb : d46864 q = 1) : d356693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39756, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39756, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39757 q = 1) (hb : d46864 q = 1) : d356694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39757, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39757, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39758 q = 1) (hb : d46864 q = 1) : d356695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39758, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39758, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39759 q = 1) (hb : d46864 q = 1) : d356696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39759, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39759, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39760 q = 1) (hb : d46864 q = 1) : d356697 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39760, d356697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39760, d356697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96362 (p : Pattern) (ha : d39763 p = 1) (hb : d46864 p = 1) : d356700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d46864 q = 1) : d356678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96357 q ha hb
    | true =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d46864 q = 1) : d356679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d46864 q = 1) : d356682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96358 q ha hb
    | true =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d46864 q = 1) : d356683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d46864 q = 1) : d356684 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39748 q = 1) (hb : d46864 q = 1) : d356685 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39748, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39748, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39749 q = 1) (hb : d46864 q = 1) : d356686 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39749, d356686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39749, d356686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39763 q = 1) (hb : d46864 q = 1) : d356700 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39763, d356700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39763, d356700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96363 (p : Pattern) (ha : d39764 p = 1) (hb : d46864 p = 1) : d356701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d46864 q = 1) : d356682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96358 q ha hb
    | true =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d46864 q = 1) : d356683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d46864 q = 1) : d356688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39752 q = 1) (hb : d46864 q = 1) : d356689 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39752, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39752, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39753 q = 1) (hb : d46864 q = 1) : d356690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39753, d356690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39753, d356690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39764 q = 1) (hb : d46864 q = 1) : d356701 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39764, d356701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39764, d356701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96364 (p : Pattern) (ha : d39770 p = 1) (hb : d46864 p = 1) : d356707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39755 q = 1) (hb : d46864 q = 1) : d356692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39755, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96359 q ha hb
    | true =>
      simp only [d39755, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96360 q ha hb
  have h2 (q : Pattern) (ha : d39756 q = 1) (hb : d46864 q = 1) : d356693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39756, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39756, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39757 q = 1) (hb : d46864 q = 1) : d356694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39757, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39757, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39758 q = 1) (hb : d46864 q = 1) : d356695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39758, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39758, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39759 q = 1) (hb : d46864 q = 1) : d356696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39759, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39759, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39765 q = 1) (hb : d46864 q = 1) : d356702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39765, d356702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96362 q ha hb
    | true =>
      simp only [d39765, d356702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96363 q ha hb
  have h7 (q : Pattern) (ha : d39766 q = 1) (hb : d46864 q = 1) : d356703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39766, d356703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39766, d356703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39767 q = 1) (hb : d46864 q = 1) : d356704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39767, d356704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39767, d356704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39768 q = 1) (hb : d46864 q = 1) : d356705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39768, d356705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39768, d356705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39769 q = 1) (hb : d46864 q = 1) : d356706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39769, d356706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39769, d356706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39770 q = 1) (hb : d46864 q = 1) : d356707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39770, d356707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39770, d356707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96365 (p : Pattern) (ha : d39926 p = 1) (hb : d46864 p = 1) : d356788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39755 q = 1) (hb : d46864 q = 1) : d356692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39755, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96359 q ha hb
    | true =>
      simp only [d39755, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96360 q ha hb
  have h2 (q : Pattern) (ha : d39756 q = 1) (hb : d46864 q = 1) : d356693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39756, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39756, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39757 q = 1) (hb : d46864 q = 1) : d356694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39757, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39757, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39758 q = 1) (hb : d46864 q = 1) : d356695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39758, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39758, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39759 q = 1) (hb : d46864 q = 1) : d356696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39759, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39759, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39921 q = 1) (hb : d46864 q = 1) : d356783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39921, d356783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96360 q ha hb
    | true =>
      simp only [d39921, d356783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39922 q = 1) (hb : d46864 q = 1) : d356784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39922, d356784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39922, d356784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39923 q = 1) (hb : d46864 q = 1) : d356785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39923, d356785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39923, d356785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39924 q = 1) (hb : d46864 q = 1) : d356786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39924, d356786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39924, d356786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39925 q = 1) (hb : d46864 q = 1) : d356787 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39925, d356787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39925, d356787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39926 q = 1) (hb : d46864 q = 1) : d356788 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39926, d356788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39926, d356788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96366 (p : Pattern) (ha : d39932 p = 1) (hb : d46864 p = 1) : d356794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39921 q = 1) (hb : d46864 q = 1) : d356783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39921, d356783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96360 q ha hb
    | true =>
      simp only [d39921, d356783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39922 q = 1) (hb : d46864 q = 1) : d356784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39922, d356784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39922, d356784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39923 q = 1) (hb : d46864 q = 1) : d356785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39923, d356785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39923, d356785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39924 q = 1) (hb : d46864 q = 1) : d356786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39924, d356786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39924, d356786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39925 q = 1) (hb : d46864 q = 1) : d356787 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39925, d356787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39925, d356787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39927 q = 1) (hb : d46864 q = 1) : d356789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39927, d356789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96363 q ha hb
    | true =>
      simp only [d39927, d356789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39928 q = 1) (hb : d46864 q = 1) : d356790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39928, d356790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39928, d356790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39929 q = 1) (hb : d46864 q = 1) : d356791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39929, d356791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39929, d356791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39930 q = 1) (hb : d46864 q = 1) : d356792 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39930, d356792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39930, d356792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39931 q = 1) (hb : d46864 q = 1) : d356793 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39931, d356793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39931, d356793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39932 q = 1) (hb : d46864 q = 1) : d356794 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39932, d356794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39932, d356794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96367 (p : Pattern) (ha : d39941 p = 1) (hb : d46864 p = 1) : d356803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39927 q = 1) (hb : d46864 q = 1) : d356789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39927, d356789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96363 q ha hb
    | true =>
      simp only [d39927, d356789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39928 q = 1) (hb : d46864 q = 1) : d356790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39928, d356790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39928, d356790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39929 q = 1) (hb : d46864 q = 1) : d356791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39929, d356791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39929, d356791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39930 q = 1) (hb : d46864 q = 1) : d356792 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39930, d356792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39930, d356792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39931 q = 1) (hb : d46864 q = 1) : d356793 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39931, d356793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39931, d356793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39941 q = 1) (hb : d46864 q = 1) : d356803 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39941, d356803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39941, d356803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96368 (p : Pattern) (ha : d39971 p = 1) (hb : d46864 p = 1) : d356819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39962 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96352 q ha hb
  have h2 (q : Pattern) (ha : d39717 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96352 q ha hb
    | true =>
      simp only [d39717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39963 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39718 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39964 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39965 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39966 q = 1) (hb : d46864 q = 1) : d356809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39966, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39966, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96353 q ha hb
  have h8 (q : Pattern) (ha : d39722 q = 1) (hb : d46864 q = 1) : d356653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96353 q ha hb
    | true =>
      simp only [d39722, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39967 q = 1) (hb : d46864 q = 1) : d356810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39967, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39967, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39723 q = 1) (hb : d46864 q = 1) : d356654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39723, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39968 q = 1) (hb : d46864 q = 1) : d356811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39968, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39968, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d39969 q = 1) (hb : d46864 q = 1) : d356812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39969, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d39969, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d39970 q = 1) (hb : d46864 q = 1) : d356813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39970, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39970, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39947 q = 1) (hb : d46864 q = 1) : d356809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39947, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39947, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96350 q ha hb
  have h15 (q : Pattern) (ha : d39705 q = 1) (hb : d46864 q = 1) : d356653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96350 q ha hb
    | true =>
      simp only [d39705, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d39948 q = 1) (hb : d46864 q = 1) : d356810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39948, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d39948, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d39706 q = 1) (hb : d46864 q = 1) : d356654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d39706, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d39949 q = 1) (hb : d46864 q = 1) : d356811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39949, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d39949, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d39950 q = 1) (hb : d46864 q = 1) : d356812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39950, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d39950, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d39956 q = 1) (hb : d46864 q = 1) : d356818 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39956, d356818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d39956, d356818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d39971 q = 1) (hb : d46864 q = 1) : d356819 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39971, d356819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39971, d356819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro96369 (p : Pattern) (ha : d39976 p = 1) (hb : d46864 p = 1) : d356829 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39966 q = 1) (hb : d46864 q = 1) : d356809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39966, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39966, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96353 q ha hb
  have h2 (q : Pattern) (ha : d39722 q = 1) (hb : d46864 q = 1) : d356653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96353 q ha hb
    | true =>
      simp only [d39722, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39967 q = 1) (hb : d46864 q = 1) : d356810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39967, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39967, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39723 q = 1) (hb : d46864 q = 1) : d356654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39723, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39968 q = 1) (hb : d46864 q = 1) : d356811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39968, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39968, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39969 q = 1) (hb : d46864 q = 1) : d356812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39969, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39969, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39975 q = 1) (hb : d46864 q = 1) : d356818 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39975, d356818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39975, d356818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d46864 q = 1) : d356824 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d356824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d356824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96355 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d46864 q = 1) : d356665 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d356665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96355 q ha hb
    | true =>
      simp only [d10412, d356665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d46864 q = 1) : d356825 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d356825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d356825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d46864 q = 1) : d356666 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d356666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, d356666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d46864 q = 1) : d356826 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d356826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d356826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d46864 q = 1) : d356827 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d356827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, d356827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d46864 q = 1) : d356828 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d356828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, d356828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39976 q = 1) (hb : d46864 q = 1) : d356829 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39976, d356829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39976, d356829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96370 (p : Pattern) (ha : d39995 p = 1) (hb : d46864 p = 1) : d356848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39977 q = 1) (hb : d46864 q = 1) : d356830 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39977, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96368 q ha hb
    | true =>
      simp only [d39977, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96369 q ha hb
  have h2 (q : Pattern) (ha : d39978 q = 1) (hb : d46864 q = 1) : d356831 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39978, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39978, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39979 q = 1) (hb : d46864 q = 1) : d356832 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39979, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39979, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39985 q = 1) (hb : d46864 q = 1) : d356838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39985, d356838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39985, d356838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39994 q = 1) (hb : d46864 q = 1) : d356847 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39994, d356847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39994, d356847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39995 q = 1) (hb : d46864 q = 1) : d356848 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39995, d356848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39995, d356848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96371 (p : Pattern) (ha : d40082 p = 1) (hb : d46864 p = 1) : d356880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39996 q = 1) (hb : d46864 q = 1) : d356849 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39996, d356849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96370 q ha hb
    | true =>
      simp only [d39996, d356849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39997 q = 1) (hb : d46864 q = 1) : d356850 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39997, d356850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39997, d356850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40079 q = 1) (hb : d46864 q = 1) : d356877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40079, d356877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40079, d356877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40080 q = 1) (hb : d46864 q = 1) : d356878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40080, d356878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40080, d356878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40081 q = 1) (hb : d46864 q = 1) : d356879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40081, d356879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40081, d356879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40082 q = 1) (hb : d46864 q = 1) : d356880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40082, d356880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40082, d356880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96372 (p : Pattern) (ha : d40088 p = 1) (hb : d46864 p = 1) : d356886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40083 q = 1) (hb : d46864 q = 1) : d356881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40083, d356881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96371 q ha hb
    | true =>
      simp only [d40083, d356881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40084 q = 1) (hb : d46864 q = 1) : d356882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40084, d356882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40084, d356882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40085 q = 1) (hb : d46864 q = 1) : d356883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40085, d356883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40085, d356883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40086 q = 1) (hb : d46864 q = 1) : d356884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40086, d356884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40086, d356884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40087 q = 1) (hb : d46864 q = 1) : d356885 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40087, d356885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40087, d356885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40088 q = 1) (hb : d46864 q = 1) : d356886 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40088, d356886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40088, d356886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96373 (p : Pattern) (ha : d39775 p = 1) (hb : d46864 p = 1) : d356712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d46864 q = 1) : d356678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96357 q ha hb
    | true =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d46864 q = 1) : d356679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d46864 q = 1) : d356682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96358 q ha hb
    | true =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d46864 q = 1) : d356683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d46864 q = 1) : d356684 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39748 q = 1) (hb : d46864 q = 1) : d356685 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39748, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39748, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39774 q = 1) (hb : d46864 q = 1) : d356711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39774, d356711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39774, d356711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39775 q = 1) (hb : d46864 q = 1) : d356712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39775, d356712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39775, d356712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96374 (p : Pattern) (ha : d39777 p = 1) (hb : d46864 p = 1) : d356714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d46864 q = 1) : d356682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96358 q ha hb
    | true =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d46864 q = 1) : d356683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d46864 q = 1) : d356688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39752 q = 1) (hb : d46864 q = 1) : d356689 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39752, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39752, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39776 q = 1) (hb : d46864 q = 1) : d356713 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39776, d356713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39776, d356713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39777 q = 1) (hb : d46864 q = 1) : d356714 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39777, d356714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39777, d356714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96375 (p : Pattern) (ha : d39784 p = 1) (hb : d46864 p = 1) : d356721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d46864 q = 1) : d356678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96357 q ha hb
    | true =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d46864 q = 1) : d356679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d46864 q = 1) : d356682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96358 q ha hb
    | true =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d46864 q = 1) : d356683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d46864 q = 1) : d356684 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39782 q = 1) (hb : d46864 q = 1) : d356719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39782, d356719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39782, d356719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39783 q = 1) (hb : d46864 q = 1) : d356720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39783, d356720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39783, d356720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39784 q = 1) (hb : d46864 q = 1) : d356721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39784, d356721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39784, d356721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96376 (p : Pattern) (ha : d39787 p = 1) (hb : d46864 p = 1) : d356724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d46864 q = 1) : d356682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96358 q ha hb
    | true =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d46864 q = 1) : d356683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d46864 q = 1) : d356688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39785 q = 1) (hb : d46864 q = 1) : d356722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39785, d356722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39785, d356722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39786 q = 1) (hb : d46864 q = 1) : d356723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39786, d356723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39786, d356723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39787 q = 1) (hb : d46864 q = 1) : d356724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39787, d356724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39787, d356724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96377 (p : Pattern) (ha : d30198 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96342 q ha hb
    | true =>
      simp only [d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30079 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30080 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30081 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30198 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96378 (p : Pattern) (ha : d30204 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30199 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96377 q ha hb
    | true =>
      simp only [d30199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30200 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30201 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30202 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30088 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96344 q ha hb
    | true =>
      simp only [d30088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30089 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30090 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30091 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30203 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30098 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96346 q ha hb
    | true =>
      simp only [d30098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30099 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30100 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30101 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d30102 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d30204 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96379 (p : Pattern) (ha : d39794 p = 1) (hb : d46864 p = 1) : d356660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30098 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96346 q ha hb
    | true =>
      simp only [d30098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30099 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30100 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30101 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39705 q = 1) (hb : d46864 q = 1) : d356653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96350 q ha hb
    | true =>
      simp only [d39705, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39706 q = 1) (hb : d46864 q = 1) : d356654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39706, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39707 q = 1) (hb : d46864 q = 1) : d356655 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39707, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39707, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39708 q = 1) (hb : d46864 q = 1) : d356656 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39708, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39708, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39709 q = 1) (hb : d46864 q = 1) : d356657 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39709, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39709, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39727 q = 1) (hb : d46864 q = 1) : d356659 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39727, d356659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39727, d356659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39794 q = 1) (hb : d46864 q = 1) : d356660 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39794, d356660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39794, d356660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96380 (p : Pattern) (ha : d39800 p = 1) (hb : d46864 p = 1) : d356733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39791 q = 1) (hb : d46864 q = 1) : d356728 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39791, d356728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96378 q ha hb
    | true =>
      simp only [d39791, d356728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96351 q ha hb
  have h2 (q : Pattern) (ha : d39792 q = 1) (hb : d46864 q = 1) : d356729 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39792, d356729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39792, d356729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39793 q = 1) (hb : d46864 q = 1) : d356730 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39793, d356730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39793, d356730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39795 q = 1) (hb : d46864 q = 1) : d356661 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39795, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96351 q ha hb
    | true =>
      simp only [d39795, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96379 q ha hb
  have h5 (q : Pattern) (ha : d39796 q = 1) (hb : d46864 q = 1) : d356662 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39796, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39796, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39797 q = 1) (hb : d46864 q = 1) : d356663 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39797, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39797, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39798 q = 1) (hb : d46864 q = 1) : d356731 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39798, d356731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39798, d356731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39729 q = 1) (hb : d46864 q = 1) : d356661 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39729, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96351 q ha hb
    | true =>
      simp only [d39729, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96354 q ha hb
  have h9 (q : Pattern) (ha : d39730 q = 1) (hb : d46864 q = 1) : d356662 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39730, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39730, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39731 q = 1) (hb : d46864 q = 1) : d356663 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39731, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39731, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39734 q = 1) (hb : d46864 q = 1) : d356671 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39734, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96354 q ha hb
    | true =>
      simp only [d39734, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96356 q ha hb
  have h12 (q : Pattern) (ha : d39735 q = 1) (hb : d46864 q = 1) : d356672 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39735, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39735, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39736 q = 1) (hb : d46864 q = 1) : d356673 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39736, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39736, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39737 q = 1) (hb : d46864 q = 1) : d356674 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39737, d356674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39737, d356674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d39799 q = 1) (hb : d46864 q = 1) : d356732 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39799, d356732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39799, d356732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d39800 q = 1) (hb : d46864 q = 1) : d356733 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39800, d356733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d39800, d356733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro96381 (p : Pattern) (ha : d39806 p = 1) (hb : d46864 p = 1) : d356739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39801 q = 1) (hb : d46864 q = 1) : d356734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39801, d356734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96380 q ha hb
    | true =>
      simp only [d39801, d356734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39802 q = 1) (hb : d46864 q = 1) : d356735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39802, d356735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39802, d356735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39741 q = 1) (hb : d46864 q = 1) : d356678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96357 q ha hb
    | true =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39742 q = 1) (hb : d46864 q = 1) : d356679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39803 q = 1) (hb : d46864 q = 1) : d356736 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39803, d356736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39803, d356736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39804 q = 1) (hb : d46864 q = 1) : d356737 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39804, d356737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39804, d356737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39805 q = 1) (hb : d46864 q = 1) : d356738 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39805, d356738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39805, d356738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39806 q = 1) (hb : d46864 q = 1) : d356739 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39806, d356739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39806, d356739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96382 (p : Pattern) (ha : d39861 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96343 q ha hb
    | true =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30309 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30310 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30311 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5238 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96349 q ha hb
  have h7 (q : Pattern) (ha : d5239 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2047 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96349 q ha hb
    | true =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2048 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5243 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2061 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5244 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5245 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d39861 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro96383 (p : Pattern) (ha : d39867 p = 1) (hb : d46864 p = 1) : d356742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39717 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96352 q ha hb
    | true =>
      simp only [d39717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39718 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39719 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39720 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39722 q = 1) (hb : d46864 q = 1) : d356653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96353 q ha hb
    | true =>
      simp only [d39722, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39723 q = 1) (hb : d46864 q = 1) : d356654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39723, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39724 q = 1) (hb : d46864 q = 1) : d356655 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39724, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39724, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39725 q = 1) (hb : d46864 q = 1) : d356656 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39725, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39725, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39726 q = 1) (hb : d46864 q = 1) : d356657 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39726, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39726, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39862 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96382 q ha hb
    | true =>
      simp only [d39862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39863 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d39864 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39865 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d39866 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39867 q = 1) (hb : d46864 q = 1) : d356742 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39867, d356742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39867, d356742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96384 (p : Pattern) (ha : d39871 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96343 q ha hb
    | true =>
      simp only [d30082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5238 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96349 q ha hb
  have h4 (q : Pattern) (ha : d5239 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39868 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d39868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2047 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96349 q ha hb
    | true =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2048 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30103 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d39869 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d39869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39870 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d39870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5243 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h12 (q : Pattern) (ha : d2061 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5244 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5245 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39871 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96385 (p : Pattern) (ha : d39877 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39872 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96384 q ha hb
    | true =>
      simp only [d39872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39873 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39874 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39875 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39876 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39877 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96386 (p : Pattern) (ha : d39883 p = 1) (hb : d46864 p = 1) : d356748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39729 q = 1) (hb : d46864 q = 1) : d356661 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39729, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96351 q ha hb
    | true =>
      simp only [d39729, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96354 q ha hb
  have h2 (q : Pattern) (ha : d39730 q = 1) (hb : d46864 q = 1) : d356662 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39730, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39730, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39731 q = 1) (hb : d46864 q = 1) : d356663 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39731, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39731, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39734 q = 1) (hb : d46864 q = 1) : d356671 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39734, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96354 q ha hb
    | true =>
      simp only [d39734, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96356 q ha hb
  have h5 (q : Pattern) (ha : d39735 q = 1) (hb : d46864 q = 1) : d356672 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39735, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39735, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39736 q = 1) (hb : d46864 q = 1) : d356673 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39736, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39736, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39737 q = 1) (hb : d46864 q = 1) : d356674 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39737, d356674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39737, d356674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39878 q = 1) (hb : d46864 q = 1) : d356743 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39878, d356743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96383 q ha hb
    | true =>
      simp only [d39878, d356743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96385 q ha hb
  have h9 (q : Pattern) (ha : d39879 q = 1) (hb : d46864 q = 1) : d356744 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39879, d356744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39879, d356744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39880 q = 1) (hb : d46864 q = 1) : d356745 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39880, d356745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39880, d356745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39881 q = 1) (hb : d46864 q = 1) : d356746 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39881, d356746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39881, d356746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d39882 q = 1) (hb : d46864 q = 1) : d356747 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39882, d356747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39882, d356747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39883 q = 1) (hb : d46864 q = 1) : d356748 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39883, d356748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39883, d356748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro96387 (p : Pattern) (ha : d39889 p = 1) (hb : d46864 p = 1) : d356754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39884 q = 1) (hb : d46864 q = 1) : d356749 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39884, d356749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96386 q ha hb
    | true =>
      simp only [d39884, d356749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39885 q = 1) (hb : d46864 q = 1) : d356750 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39885, d356750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39885, d356750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39886 q = 1) (hb : d46864 q = 1) : d356751 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39886, d356751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39886, d356751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39887 q = 1) (hb : d46864 q = 1) : d356752 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39887, d356752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39887, d356752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39888 q = 1) (hb : d46864 q = 1) : d356753 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39888, d356753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39888, d356753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39889 q = 1) (hb : d46864 q = 1) : d356754 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39889, d356754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39889, d356754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96388 (p : Pattern) (ha : d46864 p = 1) (hb : d281023 p = 1) : d356760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39778 q = 1) (hb : d46864 q = 1) : d356715 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39778, d356715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96373 q ha hb
    | true =>
      simp only [d39778, d356715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96374 q ha hb
  have h2 (q : Pattern) (ha : d39779 q = 1) (hb : d46864 q = 1) : d356716 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39779, d356716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39779, d356716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39780 q = 1) (hb : d46864 q = 1) : d356717 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39780, d356717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39780, d356717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39781 q = 1) (hb : d46864 q = 1) : d356718 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39781, d356718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39781, d356718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39788 q = 1) (hb : d46864 q = 1) : d356725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39788, d356725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96375 q ha hb
    | true =>
      simp only [d39788, d356725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96376 q ha hb
  have h6 (q : Pattern) (ha : d39789 q = 1) (hb : d46864 q = 1) : d356726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39789, d356726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39789, d356726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39790 q = 1) (hb : d46864 q = 1) : d356727 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39790, d356727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39790, d356727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39807 q = 1) (hb : d46864 q = 1) : d356740 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39807, d356740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96381 q ha hb
    | true =>
      simp only [d39807, d356740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96359 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d281019 q = 1) : d356741 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281019, d356741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d281019, d356741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d39890 q = 1) (hb : d46864 q = 1) : d356755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39890, d356755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96387 q ha hb
    | true =>
      simp only [d39890, d356755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39891 q = 1) (hb : d46864 q = 1) : d356756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39891, d356756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39891, d356756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d281020 q = 1) : d356757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281020, d356757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d281020, d356757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d281021 q = 1) : d356758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281021, d356758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d281021, d356758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d281022 q = 1) : d356759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281022, d356759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d281022, d356759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d281023 q = 1) : d356760 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d281023, d356760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281023, d356760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96389 (p : Pattern) (ha : d39896 p = 1) (hb : d46864 p = 1) : d356761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d46864 q = 1) : d356678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96357 q ha hb
    | true =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d46864 q = 1) : d356679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d46864 q = 1) : d356682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96358 q ha hb
    | true =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d46864 q = 1) : d356683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d46864 q = 1) : d356684 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39748 q = 1) (hb : d46864 q = 1) : d356685 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39748, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39748, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39774 q = 1) (hb : d46864 q = 1) : d356711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39774, d356711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39774, d356711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39896 q = 1) (hb : d46864 q = 1) : d356761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39896, d356761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39896, d356761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96390 (p : Pattern) (ha : d39897 p = 1) (hb : d46864 p = 1) : d356762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d46864 q = 1) : d356682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96358 q ha hb
    | true =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d46864 q = 1) : d356683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d46864 q = 1) : d356688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39752 q = 1) (hb : d46864 q = 1) : d356689 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39752, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39752, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39776 q = 1) (hb : d46864 q = 1) : d356713 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39776, d356713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39776, d356713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39897 q = 1) (hb : d46864 q = 1) : d356762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39897, d356762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39897, d356762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96391 (p : Pattern) (ha : d39902 p = 1) (hb : d46864 p = 1) : d356767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d46864 q = 1) : d356678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96357 q ha hb
    | true =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d46864 q = 1) : d356679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d46864 q = 1) : d356682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96358 q ha hb
    | true =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d46864 q = 1) : d356683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d46864 q = 1) : d356684 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39782 q = 1) (hb : d46864 q = 1) : d356719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39782, d356719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39782, d356719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39783 q = 1) (hb : d46864 q = 1) : d356720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39783, d356720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39783, d356720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39902 q = 1) (hb : d46864 q = 1) : d356767 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39902, d356767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39902, d356767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96392 (p : Pattern) (ha : d39903 p = 1) (hb : d46864 p = 1) : d356768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d46864 q = 1) : d356682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96358 q ha hb
    | true =>
      simp only [d39745, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d46864 q = 1) : d356683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d46864 q = 1) : d356688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39785 q = 1) (hb : d46864 q = 1) : d356722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39785, d356722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39785, d356722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39786 q = 1) (hb : d46864 q = 1) : d356723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39786, d356723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39786, d356723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39903 q = 1) (hb : d46864 q = 1) : d356768 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39903, d356768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39903, d356768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96393 (p : Pattern) (ha : d39907 p = 1) (hb : d46864 p = 1) : d356772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39801 q = 1) (hb : d46864 q = 1) : d356734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39801, d356734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96380 q ha hb
    | true =>
      simp only [d39801, d356734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39802 q = 1) (hb : d46864 q = 1) : d356735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39802, d356735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39802, d356735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39741 q = 1) (hb : d46864 q = 1) : d356678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96357 q ha hb
    | true =>
      simp only [d39741, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39742 q = 1) (hb : d46864 q = 1) : d356679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39803 q = 1) (hb : d46864 q = 1) : d356736 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39803, d356736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39803, d356736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39804 q = 1) (hb : d46864 q = 1) : d356737 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39804, d356737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39804, d356737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39805 q = 1) (hb : d46864 q = 1) : d356738 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39805, d356738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39805, d356738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39907 q = 1) (hb : d46864 q = 1) : d356772 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39907, d356772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39907, d356772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96394 (p : Pattern) (ha : d39913 p = 1) (hb : d46864 p = 1) : d356775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39884 q = 1) (hb : d46864 q = 1) : d356749 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39884, d356749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96386 q ha hb
    | true =>
      simp only [d39884, d356749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39885 q = 1) (hb : d46864 q = 1) : d356750 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39885, d356750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39885, d356750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39886 q = 1) (hb : d46864 q = 1) : d356751 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39886, d356751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39886, d356751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39887 q = 1) (hb : d46864 q = 1) : d356752 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39887, d356752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39887, d356752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39888 q = 1) (hb : d46864 q = 1) : d356753 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39888, d356753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39888, d356753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39913 q = 1) (hb : d46864 q = 1) : d356775 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39913, d356775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39913, d356775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96395 (p : Pattern) (ha : d46864 p = 1) (hb : d281028 p = 1) : d356781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39778 q = 1) (hb : d46864 q = 1) : d356715 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39778, d356715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96373 q ha hb
    | true =>
      simp only [d39778, d356715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96374 q ha hb
  have h2 (q : Pattern) (ha : d39779 q = 1) (hb : d46864 q = 1) : d356716 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39779, d356716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39779, d356716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39780 q = 1) (hb : d46864 q = 1) : d356717 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39780, d356717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39780, d356717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39781 q = 1) (hb : d46864 q = 1) : d356718 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39781, d356718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39781, d356718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39788 q = 1) (hb : d46864 q = 1) : d356725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39788, d356725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96375 q ha hb
    | true =>
      simp only [d39788, d356725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96376 q ha hb
  have h6 (q : Pattern) (ha : d39789 q = 1) (hb : d46864 q = 1) : d356726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39789, d356726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39789, d356726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39790 q = 1) (hb : d46864 q = 1) : d356727 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39790, d356727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39790, d356727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39807 q = 1) (hb : d46864 q = 1) : d356740 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39807, d356740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96381 q ha hb
    | true =>
      simp only [d39807, d356740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96359 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d281019 q = 1) : d356741 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281019, d356741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d281019, d356741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d39890 q = 1) (hb : d46864 q = 1) : d356755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39890, d356755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96387 q ha hb
    | true =>
      simp only [d39890, d356755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39891 q = 1) (hb : d46864 q = 1) : d356756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39891, d356756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39891, d356756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d281020 q = 1) : d356757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281020, d356757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d281020, d356757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d281021 q = 1) : d356758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281021, d356758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d281021, d356758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d281022 q = 1) : d356759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281022, d356759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d281022, d356759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d39898 q = 1) (hb : d46864 q = 1) : d356763 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39898, d356763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96389 q ha hb
    | true =>
      simp only [d39898, d356763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96390 q ha hb
  have h16 (q : Pattern) (ha : d39899 q = 1) (hb : d46864 q = 1) : d356764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39899, d356764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39899, d356764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d39900 q = 1) (hb : d46864 q = 1) : d356765 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39900, d356765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d39900, d356765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d39901 q = 1) (hb : d46864 q = 1) : d356766 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39901, d356766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39901, d356766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d39904 q = 1) (hb : d46864 q = 1) : d356769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39904, d356769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96391 q ha hb
    | true =>
      simp only [d39904, d356769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96392 q ha hb
  have h20 (q : Pattern) (ha : d39905 q = 1) (hb : d46864 q = 1) : d356770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39905, d356770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39905, d356770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d39906 q = 1) (hb : d46864 q = 1) : d356771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39906, d356771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d39906, d356771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d39908 q = 1) (hb : d46864 q = 1) : d356773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39908, d356773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96393 q ha hb
    | true =>
      simp only [d39908, d356773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96362 q ha hb
  have h23 (q : Pattern) (ha : d46864 q = 1) (hb : d281024 q = 1) : d356774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281024, d356774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d281024, d356774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d39914 q = 1) (hb : d46864 q = 1) : d356776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39914, d356776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96394 q ha hb
    | true =>
      simp only [d39914, d356776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d39915 q = 1) (hb : d46864 q = 1) : d356777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39915, d356777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d39915, d356777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d46864 q = 1) (hb : d281025 q = 1) : d356778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281025, d356778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d281025, d356778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d46864 q = 1) (hb : d281026 q = 1) : d356779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281026, d356779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d281026, d356779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d46864 q = 1) (hb : d281027 q = 1) : d356780 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281027, d356780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d281027, d356780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d46864 q = 1) (hb : d281028 q = 1) : d356781 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d281028, d356781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d281028, d356781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro96396 (p : Pattern) (ha : d46864 p = 1) (hb : d281035 p = 1) : d356801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39908 q = 1) (hb : d46864 q = 1) : d356773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39908, d356773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96393 q ha hb
    | true =>
      simp only [d39908, d356773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96362 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d281024 q = 1) : d356774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281024, d356774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d281024, d356774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d39914 q = 1) (hb : d46864 q = 1) : d356776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39914, d356776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96394 q ha hb
    | true =>
      simp only [d39914, d356776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39915 q = 1) (hb : d46864 q = 1) : d356777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39915, d356777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39915, d356777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d281025 q = 1) : d356778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281025, d356778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281025, d356778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d281033 q = 1) : d356799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281033, d356799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281033, d356799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d281034 q = 1) : d356800 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281034, d356800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281034, d356800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d281035 q = 1) : d356801 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d281035, d356801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281035, d356801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96397 (p : Pattern) (ha : d30413 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30399 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96377 q ha hb
  have h2 (q : Pattern) (ha : d30199 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96377 q ha hb
    | true =>
      simp only [d30199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30400 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30200 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30401 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30402 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30403 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96344 q ha hb
  have h8 (q : Pattern) (ha : d30088 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96344 q ha hb
    | true =>
      simp only [d30088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30404 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30089 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30405 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30406 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30407 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30408 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96346 q ha hb
  have h15 (q : Pattern) (ha : d30098 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96346 q ha hb
    | true =>
      simp only [d30098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d30409 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d30409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30099 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d30099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d30410 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d30410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d30411 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d30411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d30412 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d30413 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro96398 (p : Pattern) (ha : d39952 p = 1) (hb : d46864 p = 1) : d356814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30403 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96344 q ha hb
  have h2 (q : Pattern) (ha : d30088 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96344 q ha hb
    | true =>
      simp only [d30088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30404 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30089 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30405 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30406 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30408 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96346 q ha hb
  have h8 (q : Pattern) (ha : d30098 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96346 q ha hb
    | true =>
      simp only [d30098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30409 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30099 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30410 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30411 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30412 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39947 q = 1) (hb : d46864 q = 1) : d356809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39947, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39947, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96350 q ha hb
  have h15 (q : Pattern) (ha : d39705 q = 1) (hb : d46864 q = 1) : d356653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96350 q ha hb
    | true =>
      simp only [d39705, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d39948 q = 1) (hb : d46864 q = 1) : d356810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39948, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d39948, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d39706 q = 1) (hb : d46864 q = 1) : d356654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d39706, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d39949 q = 1) (hb : d46864 q = 1) : d356811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39949, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d39949, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d39950 q = 1) (hb : d46864 q = 1) : d356812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39950, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d39950, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d39951 q = 1) (hb : d46864 q = 1) : d356813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39951, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39951, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d39952 q = 1) (hb : d46864 q = 1) : d356814 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39952, d356814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39952, d356814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro96399 (p : Pattern) (ha : d39957 p = 1) (hb : d46864 p = 1) : d356819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30408 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96346 q ha hb
  have h2 (q : Pattern) (ha : d30098 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96346 q ha hb
    | true =>
      simp only [d30098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30409 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30099 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30410 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30411 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39947 q = 1) (hb : d46864 q = 1) : d356809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39947, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39947, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96350 q ha hb
  have h8 (q : Pattern) (ha : d39705 q = 1) (hb : d46864 q = 1) : d356653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96350 q ha hb
    | true =>
      simp only [d39705, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39948 q = 1) (hb : d46864 q = 1) : d356810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39948, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39948, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39706 q = 1) (hb : d46864 q = 1) : d356654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39706, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39949 q = 1) (hb : d46864 q = 1) : d356811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39949, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39949, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d39950 q = 1) (hb : d46864 q = 1) : d356812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39950, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d39950, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d39951 q = 1) (hb : d46864 q = 1) : d356813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39951, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39951, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39956 q = 1) (hb : d46864 q = 1) : d356818 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39956, d356818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39956, d356818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39957 q = 1) (hb : d46864 q = 1) : d356819 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39957, d356819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39957, d356819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96400 (p : Pattern) (ha : d39982 p = 1) (hb : d46864 p = 1) : d356835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39953 q = 1) (hb : d46864 q = 1) : d356815 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39953, d356815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96397 q ha hb
    | true =>
      simp only [d39953, d356815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96398 q ha hb
  have h2 (q : Pattern) (ha : d39954 q = 1) (hb : d46864 q = 1) : d356816 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39954, d356816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39954, d356816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39955 q = 1) (hb : d46864 q = 1) : d356817 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39955, d356817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39955, d356817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39958 q = 1) (hb : d46864 q = 1) : d356820 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39958, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96398 q ha hb
    | true =>
      simp only [d39958, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96399 q ha hb
  have h5 (q : Pattern) (ha : d39959 q = 1) (hb : d46864 q = 1) : d356821 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39959, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39959, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39960 q = 1) (hb : d46864 q = 1) : d356822 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39960, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39960, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39961 q = 1) (hb : d46864 q = 1) : d356823 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39961, d356823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39961, d356823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39972 q = 1) (hb : d46864 q = 1) : d356820 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39972, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96398 q ha hb
    | true =>
      simp only [d39972, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96368 q ha hb
  have h9 (q : Pattern) (ha : d39973 q = 1) (hb : d46864 q = 1) : d356821 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39973, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39973, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39974 q = 1) (hb : d46864 q = 1) : d356822 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39974, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39974, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39977 q = 1) (hb : d46864 q = 1) : d356830 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39977, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96368 q ha hb
    | true =>
      simp only [d39977, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96369 q ha hb
  have h12 (q : Pattern) (ha : d39978 q = 1) (hb : d46864 q = 1) : d356831 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39978, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39978, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39979 q = 1) (hb : d46864 q = 1) : d356832 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39979, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39979, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39980 q = 1) (hb : d46864 q = 1) : d356833 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39980, d356833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39980, d356833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d39981 q = 1) (hb : d46864 q = 1) : d356834 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39981, d356834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39981, d356834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d39982 q = 1) (hb : d46864 q = 1) : d356835 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39982, d356835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d39982, d356835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro96401 (p : Pattern) (ha : d39987 p = 1) (hb : d46864 p = 1) : d356840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39972 q = 1) (hb : d46864 q = 1) : d356820 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39972, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96398 q ha hb
    | true =>
      simp only [d39972, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96368 q ha hb
  have h2 (q : Pattern) (ha : d39973 q = 1) (hb : d46864 q = 1) : d356821 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39973, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39973, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39974 q = 1) (hb : d46864 q = 1) : d356822 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39974, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39974, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39977 q = 1) (hb : d46864 q = 1) : d356830 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39977, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96368 q ha hb
    | true =>
      simp only [d39977, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96369 q ha hb
  have h5 (q : Pattern) (ha : d39978 q = 1) (hb : d46864 q = 1) : d356831 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39978, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39978, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39979 q = 1) (hb : d46864 q = 1) : d356832 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39979, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39979, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39980 q = 1) (hb : d46864 q = 1) : d356833 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39980, d356833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39980, d356833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39985 q = 1) (hb : d46864 q = 1) : d356838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39985, d356838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39985, d356838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39986 q = 1) (hb : d46864 q = 1) : d356839 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39986, d356839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39986, d356839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39987 q = 1) (hb : d46864 q = 1) : d356840 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39987, d356840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39987, d356840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro96402 (p : Pattern) (ha : d39993 p = 1) (hb : d46864 p = 1) : d356846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39983 q = 1) (hb : d46864 q = 1) : d356836 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39983, d356836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96400 q ha hb
    | true =>
      simp only [d39983, d356836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39984 q = 1) (hb : d46864 q = 1) : d356837 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39984, d356837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39984, d356837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39988 q = 1) (hb : d46864 q = 1) : d356841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39988, d356841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96401 q ha hb
    | true =>
      simp only [d39988, d356841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39989 q = 1) (hb : d46864 q = 1) : d356842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39989, d356842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39989, d356842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39990 q = 1) (hb : d46864 q = 1) : d356843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39990, d356843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39990, d356843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39991 q = 1) (hb : d46864 q = 1) : d356844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39991, d356844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39991, d356844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39992 q = 1) (hb : d46864 q = 1) : d356845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39992, d356845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39992, d356845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39993 q = 1) (hb : d46864 q = 1) : d356846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39993, d356846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39993, d356846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96403 (p : Pattern) (ha : d40001 p = 1) (hb : d46864 p = 1) : d356854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39988 q = 1) (hb : d46864 q = 1) : d356841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39988, d356841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96401 q ha hb
    | true =>
      simp only [d39988, d356841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39989 q = 1) (hb : d46864 q = 1) : d356842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39989, d356842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39989, d356842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39996 q = 1) (hb : d46864 q = 1) : d356849 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39996, d356849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96370 q ha hb
    | true =>
      simp only [d39996, d356849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39997 q = 1) (hb : d46864 q = 1) : d356850 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39997, d356850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39997, d356850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39998 q = 1) (hb : d46864 q = 1) : d356851 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39998, d356851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39998, d356851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39999 q = 1) (hb : d46864 q = 1) : d356852 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39999, d356852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39999, d356852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40000 q = 1) (hb : d46864 q = 1) : d356853 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40000, d356853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40000, d356853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40001 q = 1) (hb : d46864 q = 1) : d356854 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40001, d356854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40001, d356854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96404 (p : Pattern) (ha : d40053 p = 1) (hb : d46864 p = 1) : d356857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39962 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96352 q ha hb
  have h2 (q : Pattern) (ha : d39717 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96352 q ha hb
    | true =>
      simp only [d39717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39963 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39718 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39964 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39965 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39966 q = 1) (hb : d46864 q = 1) : d356809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39966, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39966, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96353 q ha hb
  have h8 (q : Pattern) (ha : d39722 q = 1) (hb : d46864 q = 1) : d356653 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96353 q ha hb
    | true =>
      simp only [d39722, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39967 q = 1) (hb : d46864 q = 1) : d356810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39967, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39967, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39723 q = 1) (hb : d46864 q = 1) : d356654 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39723, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39968 q = 1) (hb : d46864 q = 1) : d356811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39968, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39968, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d39969 q = 1) (hb : d46864 q = 1) : d356812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39969, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d39969, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d39970 q = 1) (hb : d46864 q = 1) : d356813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39970, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39970, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d40048 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96382 q ha hb
  have h15 (q : Pattern) (ha : d39862 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96382 q ha hb
    | true =>
      simp only [d39862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40049 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d40049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d39863 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d39863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40050 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40051 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d40051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d40052 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d40052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d40053 q = 1) (hb : d46864 q = 1) : d356857 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40053, d356857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40053, d356857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro96405 (p : Pattern) (ha : d40059 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40054 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96384 q ha hb
  have h2 (q : Pattern) (ha : d39872 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96384 q ha hb
    | true =>
      simp only [d39872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40055 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39873 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40056 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40057 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40058 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40059 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96406 (p : Pattern) (ha : d40065 p = 1) (hb : d46864 p = 1) : d356863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39972 q = 1) (hb : d46864 q = 1) : d356820 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39972, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96398 q ha hb
    | true =>
      simp only [d39972, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96368 q ha hb
  have h2 (q : Pattern) (ha : d39973 q = 1) (hb : d46864 q = 1) : d356821 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39973, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39973, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39974 q = 1) (hb : d46864 q = 1) : d356822 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39974, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39974, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39977 q = 1) (hb : d46864 q = 1) : d356830 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39977, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96368 q ha hb
    | true =>
      simp only [d39977, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96369 q ha hb
  have h5 (q : Pattern) (ha : d39978 q = 1) (hb : d46864 q = 1) : d356831 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39978, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39978, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39979 q = 1) (hb : d46864 q = 1) : d356832 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39979, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39979, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39980 q = 1) (hb : d46864 q = 1) : d356833 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39980, d356833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39980, d356833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40060 q = 1) (hb : d46864 q = 1) : d356858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40060, d356858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96404 q ha hb
    | true =>
      simp only [d40060, d356858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96405 q ha hb
  have h9 (q : Pattern) (ha : d40061 q = 1) (hb : d46864 q = 1) : d356859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40061, d356859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40061, d356859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40062 q = 1) (hb : d46864 q = 1) : d356860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40062, d356860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40062, d356860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40063 q = 1) (hb : d46864 q = 1) : d356861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40063, d356861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40063, d356861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40064 q = 1) (hb : d46864 q = 1) : d356862 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40064, d356862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40064, d356862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40065 q = 1) (hb : d46864 q = 1) : d356863 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40065, d356863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40065, d356863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro96407 (p : Pattern) (ha : d40071 p = 1) (hb : d46864 p = 1) : d356869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40066 q = 1) (hb : d46864 q = 1) : d356864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40066, d356864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96406 q ha hb
    | true =>
      simp only [d40066, d356864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40067 q = 1) (hb : d46864 q = 1) : d356865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40067, d356865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40067, d356865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40068 q = 1) (hb : d46864 q = 1) : d356866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40068, d356866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40068, d356866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40069 q = 1) (hb : d46864 q = 1) : d356867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40069, d356867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40069, d356867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40070 q = 1) (hb : d46864 q = 1) : d356868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40070, d356868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40070, d356868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40071 q = 1) (hb : d46864 q = 1) : d356869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40071, d356869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40071, d356869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96408 (p : Pattern) (ha : d46864 p = 1) (hb : d281045 p = 1) : d356875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40002 q = 1) (hb : d46864 q = 1) : d356855 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40002, d356855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96402 q ha hb
    | true =>
      simp only [d40002, d356855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96403 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d281041 q = 1) : d356856 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281041, d356856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d281041, d356856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d40072 q = 1) (hb : d46864 q = 1) : d356870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40072, d356870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96407 q ha hb
    | true =>
      simp only [d40072, d356870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40073 q = 1) (hb : d46864 q = 1) : d356871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40073, d356871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40073, d356871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d281042 q = 1) : d356872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281042, d356872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281042, d356872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d281043 q = 1) : d356873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281043, d356873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281043, d356873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d281044 q = 1) : d356874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281044, d356874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281044, d356874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d281045 q = 1) : d356875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d281045, d356875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281045, d356875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96409 (p : Pattern) (ha : d46864 p = 1) (hb : d281051 p = 1) : d356892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39761 q = 1) (hb : d46864 q = 1) : d356698 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39761, d356698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39761, d356698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96361 q ha hb
  have h2 (q : Pattern) (ha : d39762 q = 1) (hb : d46864 q = 1) : d356699 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d39762, d356699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39762, d356699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39771 q = 1) (hb : d46864 q = 1) : d356708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39771, d356708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96361 q ha hb
    | true =>
      simp only [d39771, d356708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96364 q ha hb
  have h4 (q : Pattern) (ha : d39772 q = 1) (hb : d46864 q = 1) : d356709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d39772, d356709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39772, d356709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39773 q = 1) (hb : d46864 q = 1) : d356710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d39773, d356710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39773, d356710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d281029 q = 1) : d356782 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d281029, d356782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96388 q ha hb
    | true =>
      simp only [d281029, d356782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96395 q ha hb
  have h7 (q : Pattern) (ha : d39933 q = 1) (hb : d46864 q = 1) : d356795 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39933, d356795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96365 q ha hb
    | true =>
      simp only [d39933, d356795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96366 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d281030 q = 1) : d356796 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d281030, d356796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d281030, d356796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d281031 q = 1) : d356797 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d281031, d356797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d281031, d356797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d281032 q = 1) : d356798 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d281032, d356798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d281032, d356798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d281036 q = 1) : d356802 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d281036, d356802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281036, d356802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96396 q ha hb
  have h12 (q : Pattern) (ha : d39942 q = 1) (hb : d46864 q = 1) : d356804 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39942, d356804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39942, d356804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96367 q ha hb
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d281037 q = 1) : d356805 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d281037, d356805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d281037, d356805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d281038 q = 1) : d356806 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d281038, d356806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d281038, d356806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d281039 q = 1) : d356807 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d281039, d356807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d281039, d356807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d46864 q = 1) (hb : d281040 q = 1) : d356808 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d281040, d356808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d281040, d356808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46864 q = 1) (hb : d281046 q = 1) : d356876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d281046, d356876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281046, d356876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96408 q ha hb
  have h18 (q : Pattern) (ha : d40089 q = 1) (hb : d46864 q = 1) : d356887 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40089, d356887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40089, d356887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96372 q ha hb
  have h19 (q : Pattern) (ha : d46864 q = 1) (hb : d281047 q = 1) : d356888 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d281047, d356888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d281047, d356888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d46864 q = 1) (hb : d281048 q = 1) : d356889 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d281048, d356889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d281048, d356889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d46864 q = 1) (hb : d281049 q = 1) : d356890 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d281049, d356890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d281049, d356890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d46864 q = 1) (hb : d281050 q = 1) : d356891 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d281050, d356891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d281050, d356891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d46864 q = 1) (hb : d281051 q = 1) : d356892 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d281051, d356892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d281051, d356892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro96410 (p : Pattern) (ha : d46864 p = 1) (hb : d281057 p = 1) : d356898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d281052 q = 1) : d356893 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d281052, d356893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281052, d356893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96409 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d281053 q = 1) : d356894 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d281053, d356894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281053, d356894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d281054 q = 1) : d356895 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d281054, d356895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281054, d356895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d281055 q = 1) : d356896 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d281055, d356896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281055, d356896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d281056 q = 1) : d356897 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d281056, d356897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281056, d356897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d281057 q = 1) : d356898 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d281057, d356898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281057, d356898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96411 (p : Pattern) (ha : d18 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d18 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d18, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h7 p ha hb
theorem andIntro96412 (p : Pattern) (ha : d24 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96413 (p : Pattern) (ha : d30 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96414 (p : Pattern) (ha : d36 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96415 (p : Pattern) (ha : d42 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96416 (p : Pattern) (ha : d48 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96417 (p : Pattern) (ha : d49 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96418 (p : Pattern) (ha : d55 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96419 (p : Pattern) (ha : d60 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96420 (p : Pattern) (ha : d71 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d66 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d68 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d70 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d71 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96421 (p : Pattern) (ha : d77 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96420 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96422 (p : Pattern) (ha : d83 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96421 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96423 (p : Pattern) (ha : d89 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96422 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96424 (p : Pattern) (ha : d95 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96416 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96418 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96419 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96423 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96425 (p : Pattern) (ha : d104 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96426 (p : Pattern) (ha : d111 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96427 (p : Pattern) (ha : d213 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96428 (p : Pattern) (ha : d116 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96429 (p : Pattern) (ha : d123 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96430 (p : Pattern) (ha : d40151 p = 1) (hb : d46864 p = 1) : d46867 p = 1 := by
  have h0 (q : Pattern) (ha : d2016 q = 1) (hb : d46864 q = 1) : d46864 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40149 q = 1) (hb : d46864 q = 1) : d46865 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d40149, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40149, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d16 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40150 q = 1) (hb : d46864 q = 1) : d46866 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d40150, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40150, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h10 (q : Pattern) (ha : d40151 q = 1) (hb : d46864 q = 1) : d46867 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d40151, d46867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40151, d46867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96431 (p : Pattern) (ha : d40157 p = 1) (hb : d46864 p = 1) : d355780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40152 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96430 q ha hb
    | true =>
      simp only [d40152, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40153 q = 1) (hb : d46864 q = 1) : d355776 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40153, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40154 q = 1) (hb : d46864 q = 1) : d355777 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40154, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40155 q = 1) (hb : d46864 q = 1) : d355778 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40155, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40155, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40156 q = 1) (hb : d46864 q = 1) : d355779 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40156, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40156, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40157 q = 1) (hb : d46864 q = 1) : d355780 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40157, d355780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40157, d355780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96432 (p : Pattern) (ha : d40163 p = 1) (hb : d46864 p = 1) : d355786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40158 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40158, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96431 q ha hb
    | true =>
      simp only [d40158, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40159 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40159, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40159, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40160 q = 1) (hb : d46864 q = 1) : d355783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40160, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40160, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40161 q = 1) (hb : d46864 q = 1) : d355784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40161, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40161, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40162 q = 1) (hb : d46864 q = 1) : d355785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40162, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40162, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40163 q = 1) (hb : d46864 q = 1) : d355786 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40163, d355786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40163, d355786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96433 (p : Pattern) (ha : d40169 p = 1) (hb : d46864 p = 1) : d355792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40164 q = 1) (hb : d46864 q = 1) : d355787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40164, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96432 q ha hb
    | true =>
      simp only [d40164, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
  have h2 (q : Pattern) (ha : d40165 q = 1) (hb : d46864 q = 1) : d355788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40165, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40165, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40166 q = 1) (hb : d46864 q = 1) : d355789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40166, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40166, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40167 q = 1) (hb : d46864 q = 1) : d355790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40167, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40167, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40168 q = 1) (hb : d46864 q = 1) : d355791 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40168, d355791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40168, d355791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40169 q = 1) (hb : d46864 q = 1) : d355792 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40169, d355792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40169, d355792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro96434 (p : Pattern) (ha : d40175 p = 1) (hb : d46864 p = 1) : d355798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96433 q ha hb
    | true =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40172 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40172, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40172, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40173 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40173, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40173, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40174 q = 1) (hb : d46864 q = 1) : d355797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40174, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40174, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40175 q = 1) (hb : d46864 q = 1) : d355798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40175, d355798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40175, d355798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96435 (p : Pattern) (ha : d46864 p = 1) (hb : d289282 p = 1) : d355804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96428 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96429 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40176 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40176, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96434 q ha hb
    | true =>
      simp only [d40176, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d289278 q = 1) : d355800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289278, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d289278, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d289279 q = 1) : d355801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289279, d355801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289279, d355801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d289280 q = 1) : d355802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289280, d355802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d289280, d355802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d289281 q = 1) : d355803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289281, d355803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289281, d355803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d289282 q = 1) : d355804 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289282, d355804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289282, d355804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96436 (p : Pattern) (ha : d194 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96437 (p : Pattern) (ha : d199 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96438 (p : Pattern) (ha : d40182 p = 1) (hb : d46864 p = 1) : d355805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96433 q ha hb
    | true =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40172 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40172, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40172, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40173 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40173, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40173, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40174 q = 1) (hb : d46864 q = 1) : d355797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40174, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40174, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40182 q = 1) (hb : d46864 q = 1) : d355805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40182, d355805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40182, d355805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96439 (p : Pattern) (ha : d46864 p = 1) (hb : d289287 p = 1) : d355811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96428 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96429 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40176 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40176, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96434 q ha hb
    | true =>
      simp only [d40176, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d289278 q = 1) : d355800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289278, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d289278, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d289279 q = 1) : d355801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289279, d355801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289279, d355801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d289280 q = 1) : d355802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289280, d355802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d289280, d355802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d289281 q = 1) : d355803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289281, d355803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289281, d355803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96436 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96437 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d40183 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40183, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96438 q ha hb
    | true =>
      simp only [d40183, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
  have h23 (q : Pattern) (ha : d46864 q = 1) (hb : d289283 q = 1) : d355807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289283, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d289283, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d46864 q = 1) (hb : d289284 q = 1) : d355808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289284, d355808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d289284, d355808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d46864 q = 1) (hb : d289285 q = 1) : d355809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289285, d355809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d289285, d355809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d46864 q = 1) (hb : d289286 q = 1) : d355810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289286, d355810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d289286, d355810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d46864 q = 1) (hb : d289287 q = 1) : d355811 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289287, d355811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d289287, d355811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro96440 (p : Pattern) (ha : d46864 p = 1) (hb : d289294 p = 1) : d355816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40183 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40183, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96438 q ha hb
    | true =>
      simp only [d40183, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d289283 q = 1) : d355807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289283, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289283, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d289284 q = 1) : d355808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289284, d355808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289284, d355808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d289292 q = 1) : d355809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289292, d355809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289292, d355809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d289293 q = 1) : d355810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289293, d355810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289293, d355810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d289294 q = 1) : d355816 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289294, d355816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289294, d355816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96441 (p : Pattern) (ha : d40206 p = 1) (hb : d46864 p = 1) : d355827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40201 q = 1) (hb : d46864 q = 1) : d355822 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40201, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40201, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96431 q ha hb
  have h2 (q : Pattern) (ha : d40158 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40158, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96431 q ha hb
    | true =>
      simp only [d40158, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40202 q = 1) (hb : d46864 q = 1) : d355823 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40202, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40202, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40159 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40159, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40159, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40203 q = 1) (hb : d46864 q = 1) : d355824 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40203, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40203, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40204 q = 1) (hb : d46864 q = 1) : d355825 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40204, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40204, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40205 q = 1) (hb : d46864 q = 1) : d355826 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40205, d355826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40205, d355826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d40206 q = 1) (hb : d46864 q = 1) : d355827 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40206, d355827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40206, d355827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96442 (p : Pattern) (ha : d40212 p = 1) (hb : d46864 p = 1) : d355833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40207 q = 1) (hb : d46864 q = 1) : d355828 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40207, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96441 q ha hb
    | true =>
      simp only [d40207, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96420 q ha hb
  have h2 (q : Pattern) (ha : d40208 q = 1) (hb : d46864 q = 1) : d355829 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40208, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40208, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40209 q = 1) (hb : d46864 q = 1) : d355830 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40209, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40209, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96420 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40210 q = 1) (hb : d46864 q = 1) : d355831 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40210, d355831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40210, d355831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40211 q = 1) (hb : d46864 q = 1) : d355832 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40211, d355832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40211, d355832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40212 q = 1) (hb : d46864 q = 1) : d355833 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40212, d355833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40212, d355833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro96443 (p : Pattern) (ha : d40218 p = 1) (hb : d46864 p = 1) : d355839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40213 q = 1) (hb : d46864 q = 1) : d355834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40213, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96442 q ha hb
    | true =>
      simp only [d40213, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40214 q = 1) (hb : d46864 q = 1) : d355835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40214, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40214, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96421 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40215 q = 1) (hb : d46864 q = 1) : d355836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40215, d355836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40215, d355836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40216 q = 1) (hb : d46864 q = 1) : d355837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40216, d355837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40216, d355837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40217 q = 1) (hb : d46864 q = 1) : d355838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40217, d355838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40217, d355838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40218 q = 1) (hb : d46864 q = 1) : d355839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40218, d355839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40218, d355839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96444 (p : Pattern) (ha : d46864 p = 1) (hb : d289304 p = 1) : d355845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40219 q = 1) (hb : d46864 q = 1) : d355840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40219, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96443 q ha hb
    | true =>
      simp only [d40219, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96422 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d289300 q = 1) : d355841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289300, d355841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289300, d355841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96422 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d289301 q = 1) : d355842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289301, d355842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289301, d355842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d289302 q = 1) : d355843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289302, d355843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289302, d355843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d289303 q = 1) : d355844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289303, d355844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289303, d355844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d289304 q = 1) : d355845 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289304, d355845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289304, d355845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96445 (p : Pattern) (ha : d46864 p = 1) (hb : d289310 p = 1) : d355851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96425 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96425 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96426 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d289288 q = 1) : d355812 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289288, d355812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96435 q ha hb
    | true =>
      simp only [d289288, d355812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96439 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96427 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d289289 q = 1) : d355813 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289289, d355813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289289, d355813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d289290 q = 1) : d355814 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289290, d355814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289290, d355814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d289291 q = 1) : d355815 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289291, d355815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d289291, d355815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d289295 q = 1) : d355817 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289295, d355817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289295, d355817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96440 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d289296 q = 1) : d355818 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289296, d355818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289296, d355818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d289297 q = 1) : d355819 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289297, d355819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289297, d355819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d289298 q = 1) : d355820 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289298, d355820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289298, d355820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d289299 q = 1) : d355821 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289299, d355821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289299, d355821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46864 q = 1) (hb : d289305 q = 1) : d355846 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289305, d355846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289305, d355846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96444 q ha hb
  have h17 (q : Pattern) (ha : d46864 q = 1) (hb : d289306 q = 1) : d355847 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289306, d355847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289306, d355847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d46864 q = 1) (hb : d289307 q = 1) : d355848 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289307, d355848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289307, d355848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d46864 q = 1) (hb : d289308 q = 1) : d355849 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289308, d355849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d289308, d355849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d46864 q = 1) (hb : d289309 q = 1) : d355850 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289309, d355850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d289309, d355850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d46864 q = 1) (hb : d289310 q = 1) : d355851 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289310, d355851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289310, d355851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro96446 (p : Pattern) (ha : d406 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96447 (p : Pattern) (ha : d462 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96422 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
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
theorem andIntro96448 (p : Pattern) (ha : d40240 p = 1) (hb : d46864 p = 1) : d355861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40176 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40176, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96434 q ha hb
    | true =>
      simp only [d40176, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
  have h2 (q : Pattern) (ha : d40236 q = 1) (hb : d46864 q = 1) : d355857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40236, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40236, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40237 q = 1) (hb : d46864 q = 1) : d355858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40237, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40237, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40238 q = 1) (hb : d46864 q = 1) : d355859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40238, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40238, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40239 q = 1) (hb : d46864 q = 1) : d355860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40239, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40239, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40240 q = 1) (hb : d46864 q = 1) : d355861 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40240, d355861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40240, d355861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96449 (p : Pattern) (ha : d40247 p = 1) (hb : d46864 p = 1) : d355868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40176 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40176, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96434 q ha hb
    | true =>
      simp only [d40176, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
  have h2 (q : Pattern) (ha : d40236 q = 1) (hb : d46864 q = 1) : d355857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40236, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40236, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40237 q = 1) (hb : d46864 q = 1) : d355858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40237, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40237, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40238 q = 1) (hb : d46864 q = 1) : d355859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40238, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40238, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40239 q = 1) (hb : d46864 q = 1) : d355860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40239, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40239, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40183 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40183, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96438 q ha hb
    | true =>
      simp only [d40183, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
  have h7 (q : Pattern) (ha : d40243 q = 1) (hb : d46864 q = 1) : d355864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40243, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40243, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40244 q = 1) (hb : d46864 q = 1) : d355865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40244, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40244, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40245 q = 1) (hb : d46864 q = 1) : d355866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40245, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40245, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40246 q = 1) (hb : d46864 q = 1) : d355867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40246, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40246, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40247 q = 1) (hb : d46864 q = 1) : d355868 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40247, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40247, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96450 (p : Pattern) (ha : d40359 p = 1) (hb : d46864 p = 1) : d355933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40176 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40176, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96434 q ha hb
    | true =>
      simp only [d40176, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
  have h2 (q : Pattern) (ha : d40236 q = 1) (hb : d46864 q = 1) : d355857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40236, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40236, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40237 q = 1) (hb : d46864 q = 1) : d355858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40237, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40237, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40238 q = 1) (hb : d46864 q = 1) : d355859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40238, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40238, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40239 q = 1) (hb : d46864 q = 1) : d355860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40239, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40239, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40359 q = 1) (hb : d46864 q = 1) : d355933 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40359, d355933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40359, d355933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96451 (p : Pattern) (ha : d40252 p = 1) (hb : d46864 p = 1) : d355873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96433 q ha hb
    | true =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40172 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40172, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40172, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40173 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40173, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40173, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40251 q = 1) (hb : d46864 q = 1) : d355872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40251, d355872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40251, d355872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40252 q = 1) (hb : d46864 q = 1) : d355873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40252, d355873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40252, d355873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96452 (p : Pattern) (ha : d40259 p = 1) (hb : d46864 p = 1) : d355880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96433 q ha hb
    | true =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40172 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40172, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40172, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40257 q = 1) (hb : d46864 q = 1) : d355878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40257, d355878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40257, d355878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40258 q = 1) (hb : d46864 q = 1) : d355879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40258, d355879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40258, d355879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40259 q = 1) (hb : d46864 q = 1) : d355880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40259, d355880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40259, d355880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96453 (p : Pattern) (ha : d40264 p = 1) (hb : d46864 p = 1) : d355885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1997 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2016 q = 1) (hb : d46864 q = 1) : d46864 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d2017 q = 1) (hb : d46864 q = 1) : d276820 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2017, d276820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2017, d276820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40149 q = 1) (hb : d46864 q = 1) : d46865 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d40149, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40149, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40263 q = 1) (hb : d46864 q = 1) : d355884 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d40263, d355884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40263, d355884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d16 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d40150 q = 1) (hb : d46864 q = 1) : d46866 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d40150, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40150, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d40264 q = 1) (hb : d46864 q = 1) : d355885 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d40264, d355885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40264, d355885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96454 (p : Pattern) (ha : d40270 p = 1) (hb : d46864 p = 1) : d355891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40265 q = 1) (hb : d46864 q = 1) : d355886 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96453 q ha hb
    | true =>
      simp only [d40265, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40266 q = 1) (hb : d46864 q = 1) : d355887 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40266, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40152 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96430 q ha hb
    | true =>
      simp only [d40152, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40153 q = 1) (hb : d46864 q = 1) : d355776 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40153, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40267 q = 1) (hb : d46864 q = 1) : d355888 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40267, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40267, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40154 q = 1) (hb : d46864 q = 1) : d355777 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40154, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40268 q = 1) (hb : d46864 q = 1) : d355889 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40268, d355889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40268, d355889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40269 q = 1) (hb : d46864 q = 1) : d355890 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40269, d355890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40269, d355890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40155 q = 1) (hb : d46864 q = 1) : d355778 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40155, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40155, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40156 q = 1) (hb : d46864 q = 1) : d355779 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40156, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40156, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d40270 q = 1) (hb : d46864 q = 1) : d355891 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40270, d355891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40270, d355891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro96455 (p : Pattern) (ha : d40278 p = 1) (hb : d46864 p = 1) : d355780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40152 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96430 q ha hb
    | true =>
      simp only [d40152, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40153 q = 1) (hb : d46864 q = 1) : d355776 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40153, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40154 q = 1) (hb : d46864 q = 1) : d355777 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40154, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40276 q = 1) (hb : d46864 q = 1) : d355778 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40276, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40276, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40277 q = 1) (hb : d46864 q = 1) : d355779 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40277, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40277, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40278 q = 1) (hb : d46864 q = 1) : d355780 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40278, d355780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40278, d355780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96456 (p : Pattern) (ha : d40284 p = 1) (hb : d46864 p = 1) : d355897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40271 q = 1) (hb : d46864 q = 1) : d355892 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40271, d355892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96454 q ha hb
    | true =>
      simp only [d40271, d355892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40272 q = 1) (hb : d46864 q = 1) : d355893 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40272, d355893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40272, d355893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40273 q = 1) (hb : d46864 q = 1) : d355894 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40273, d355894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40273, d355894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40274 q = 1) (hb : d46864 q = 1) : d355895 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40274, d355895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40274, d355895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40158 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40158, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96431 q ha hb
    | true =>
      simp only [d40158, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40159 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40159, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40159, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40160 q = 1) (hb : d46864 q = 1) : d355783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40160, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40160, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40161 q = 1) (hb : d46864 q = 1) : d355784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40161, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40161, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40275 q = 1) (hb : d46864 q = 1) : d355896 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40275, d355896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40275, d355896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40279 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40279, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96455 q ha hb
    | true =>
      simp only [d40279, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40280 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40280, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40280, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40281 q = 1) (hb : d46864 q = 1) : d355783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40281, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40281, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40282 q = 1) (hb : d46864 q = 1) : d355784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40282, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40282, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40283 q = 1) (hb : d46864 q = 1) : d355785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40283, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40283, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40284 q = 1) (hb : d46864 q = 1) : d355897 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40284, d355897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40284, d355897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96457 (p : Pattern) (ha : d40290 p = 1) (hb : d46864 p = 1) : d355903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40285 q = 1) (hb : d46864 q = 1) : d355898 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40285, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96456 q ha hb
    | true =>
      simp only [d40285, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96432 q ha hb
  have h2 (q : Pattern) (ha : d40286 q = 1) (hb : d46864 q = 1) : d355899 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40286, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40286, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40287 q = 1) (hb : d46864 q = 1) : d355900 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40287, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40287, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40164 q = 1) (hb : d46864 q = 1) : d355787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40164, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96432 q ha hb
    | true =>
      simp only [d40164, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
  have h5 (q : Pattern) (ha : d40165 q = 1) (hb : d46864 q = 1) : d355788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40165, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40165, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40166 q = 1) (hb : d46864 q = 1) : d355789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40166, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40166, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40288 q = 1) (hb : d46864 q = 1) : d355901 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40288, d355901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40288, d355901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40167 q = 1) (hb : d46864 q = 1) : d355790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40167, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40167, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40289 q = 1) (hb : d46864 q = 1) : d355902 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40289, d355902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40289, d355902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40290 q = 1) (hb : d46864 q = 1) : d355903 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40290, d355903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40290, d355903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro96458 (p : Pattern) (ha : d40296 p = 1) (hb : d46864 p = 1) : d355909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40291 q = 1) (hb : d46864 q = 1) : d355904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40291, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96457 q ha hb
    | true =>
      simp only [d40291, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40292 q = 1) (hb : d46864 q = 1) : d355905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40292, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40292, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40170 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96433 q ha hb
    | true =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40171 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40293 q = 1) (hb : d46864 q = 1) : d355906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40293, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40293, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40294 q = 1) (hb : d46864 q = 1) : d355907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40294, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40294, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40295 q = 1) (hb : d46864 q = 1) : d355908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40295, d355908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40295, d355908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40296 q = 1) (hb : d46864 q = 1) : d355909 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40296, d355909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40296, d355909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96459 (p : Pattern) (ha : d40330 p = 1) (hb : d46864 p = 1) : d355798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96433 q ha hb
    | true =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40327 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40327, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40327, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40328 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40328, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40328, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40329 q = 1) (hb : d46864 q = 1) : d355797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40329, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40329, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40330 q = 1) (hb : d46864 q = 1) : d355798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40330, d355798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40330, d355798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96460 (p : Pattern) (ha : d46864 p = 1) (hb : d289320 p = 1) : d355915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40253 q = 1) (hb : d46864 q = 1) : d355874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40253, d355874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96451 q ha hb
    | true =>
      simp only [d40253, d355874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96428 q ha hb
  have h2 (q : Pattern) (ha : d40254 q = 1) (hb : d46864 q = 1) : d355875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40254, d355875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40254, d355875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40255 q = 1) (hb : d46864 q = 1) : d355876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40255, d355876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40255, d355876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40256 q = 1) (hb : d46864 q = 1) : d355877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40256, d355877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40256, d355877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40260 q = 1) (hb : d46864 q = 1) : d355881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40260, d355881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96452 q ha hb
    | true =>
      simp only [d40260, d355881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96429 q ha hb
  have h6 (q : Pattern) (ha : d40261 q = 1) (hb : d46864 q = 1) : d355882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40261, d355882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40261, d355882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40262 q = 1) (hb : d46864 q = 1) : d355883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40262, d355883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40262, d355883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40297 q = 1) (hb : d46864 q = 1) : d355910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40297, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96458 q ha hb
    | true =>
      simp only [d40297, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96434 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d289316 q = 1) : d355911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289316, d355911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d289316, d355911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d40331 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40331, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96459 q ha hb
    | true =>
      simp only [d40331, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40332 q = 1) (hb : d46864 q = 1) : d355800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40332, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40332, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d289317 q = 1) : d355912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289317, d355912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289317, d355912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d289318 q = 1) : d355913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289318, d355913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d289318, d355913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d289319 q = 1) : d355914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289319, d355914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289319, d355914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d289320 q = 1) : d355915 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289320, d355915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289320, d355915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96461 (p : Pattern) (ha : d40337 p = 1) (hb : d46864 p = 1) : d355916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96433 q ha hb
    | true =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40172 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40172, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40172, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40173 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40173, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40173, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40251 q = 1) (hb : d46864 q = 1) : d355872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40251, d355872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40251, d355872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40337 q = 1) (hb : d46864 q = 1) : d355916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40337, d355916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40337, d355916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96462 (p : Pattern) (ha : d40342 p = 1) (hb : d46864 p = 1) : d355921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96433 q ha hb
    | true =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40172 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40172, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40172, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40257 q = 1) (hb : d46864 q = 1) : d355878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40257, d355878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40257, d355878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40258 q = 1) (hb : d46864 q = 1) : d355879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40258, d355879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40258, d355879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40342 q = 1) (hb : d46864 q = 1) : d355921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40342, d355921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40342, d355921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96463 (p : Pattern) (ha : d40346 p = 1) (hb : d46864 p = 1) : d355925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40291 q = 1) (hb : d46864 q = 1) : d355904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40291, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96457 q ha hb
    | true =>
      simp only [d40291, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40292 q = 1) (hb : d46864 q = 1) : d355905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40292, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40292, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40170 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96433 q ha hb
    | true =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40171 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40293 q = 1) (hb : d46864 q = 1) : d355906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40293, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40293, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40294 q = 1) (hb : d46864 q = 1) : d355907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40294, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40294, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40295 q = 1) (hb : d46864 q = 1) : d355908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40295, d355908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40295, d355908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40346 q = 1) (hb : d46864 q = 1) : d355925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40346, d355925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40346, d355925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96464 (p : Pattern) (ha : d40351 p = 1) (hb : d46864 p = 1) : d355805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40170 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96433 q ha hb
    | true =>
      simp only [d40170, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40171 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40171, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40327 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40327, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40327, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40328 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40328, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40328, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40329 q = 1) (hb : d46864 q = 1) : d355797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40329, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40329, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40351 q = 1) (hb : d46864 q = 1) : d355805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40351, d355805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40351, d355805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96465 (p : Pattern) (ha : d46864 p = 1) (hb : d289325 p = 1) : d355931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40253 q = 1) (hb : d46864 q = 1) : d355874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40253, d355874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96451 q ha hb
    | true =>
      simp only [d40253, d355874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96428 q ha hb
  have h2 (q : Pattern) (ha : d40254 q = 1) (hb : d46864 q = 1) : d355875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40254, d355875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40254, d355875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40255 q = 1) (hb : d46864 q = 1) : d355876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40255, d355876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40255, d355876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40256 q = 1) (hb : d46864 q = 1) : d355877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40256, d355877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40256, d355877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40260 q = 1) (hb : d46864 q = 1) : d355881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40260, d355881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96452 q ha hb
    | true =>
      simp only [d40260, d355881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96429 q ha hb
  have h6 (q : Pattern) (ha : d40261 q = 1) (hb : d46864 q = 1) : d355882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40261, d355882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40261, d355882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40262 q = 1) (hb : d46864 q = 1) : d355883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40262, d355883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40262, d355883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40297 q = 1) (hb : d46864 q = 1) : d355910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40297, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96458 q ha hb
    | true =>
      simp only [d40297, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96434 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d289316 q = 1) : d355911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289316, d355911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d289316, d355911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d40331 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40331, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96459 q ha hb
    | true =>
      simp only [d40331, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40332 q = 1) (hb : d46864 q = 1) : d355800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40332, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40332, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d289317 q = 1) : d355912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289317, d355912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289317, d355912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d289318 q = 1) : d355913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289318, d355913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d289318, d355913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d289319 q = 1) : d355914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289319, d355914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289319, d355914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d40338 q = 1) (hb : d46864 q = 1) : d355917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40338, d355917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96461 q ha hb
    | true =>
      simp only [d40338, d355917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96436 q ha hb
  have h16 (q : Pattern) (ha : d40339 q = 1) (hb : d46864 q = 1) : d355918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40339, d355918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40339, d355918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40340 q = 1) (hb : d46864 q = 1) : d355919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40340, d355919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40340, d355919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40341 q = 1) (hb : d46864 q = 1) : d355920 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40341, d355920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40341, d355920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40343 q = 1) (hb : d46864 q = 1) : d355922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40343, d355922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96462 q ha hb
    | true =>
      simp only [d40343, d355922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96437 q ha hb
  have h20 (q : Pattern) (ha : d40344 q = 1) (hb : d46864 q = 1) : d355923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40344, d355923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40344, d355923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d40345 q = 1) (hb : d46864 q = 1) : d355924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40345, d355924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d40345, d355924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d40347 q = 1) (hb : d46864 q = 1) : d355926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40347, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96463 q ha hb
    | true =>
      simp only [d40347, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96438 q ha hb
  have h23 (q : Pattern) (ha : d46864 q = 1) (hb : d289321 q = 1) : d355927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289321, d355927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d289321, d355927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d40352 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40352, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96464 q ha hb
    | true =>
      simp only [d40352, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d40353 q = 1) (hb : d46864 q = 1) : d355807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40353, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d40353, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d46864 q = 1) (hb : d289322 q = 1) : d355928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289322, d355928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d289322, d355928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d46864 q = 1) (hb : d289323 q = 1) : d355929 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289323, d355929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d289323, d355929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d46864 q = 1) (hb : d289324 q = 1) : d355930 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289324, d355930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d289324, d355930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d46864 q = 1) (hb : d289325 q = 1) : d355931 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289325, d355931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d289325, d355931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro96466 (p : Pattern) (ha : d46864 p = 1) (hb : d289332 p = 1) : d355940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40347 q = 1) (hb : d46864 q = 1) : d355926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40347, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96463 q ha hb
    | true =>
      simp only [d40347, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96438 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d289321 q = 1) : d355927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289321, d355927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289321, d355927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d40352 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40352, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96464 q ha hb
    | true =>
      simp only [d40352, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40353 q = 1) (hb : d46864 q = 1) : d355807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40353, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40353, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d289322 q = 1) : d355928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289322, d355928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289322, d355928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d289330 q = 1) : d355938 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289330, d355938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289330, d355938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d289331 q = 1) : d355939 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289331, d355939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289331, d355939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d289332 q = 1) : d355940 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289332, d355940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289332, d355940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96467 (p : Pattern) (ha : d40382 p = 1) (hb : d46864 p = 1) : d355951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40372 q = 1) (hb : d46864 q = 1) : d355946 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40372, d355946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40372, d355946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96454 q ha hb
  have h2 (q : Pattern) (ha : d40271 q = 1) (hb : d46864 q = 1) : d355892 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40271, d355892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96454 q ha hb
    | true =>
      simp only [d40271, d355892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40373 q = 1) (hb : d46864 q = 1) : d355947 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40373, d355947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40373, d355947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40272 q = 1) (hb : d46864 q = 1) : d355893 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40272, d355893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40272, d355893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40374 q = 1) (hb : d46864 q = 1) : d355948 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40374, d355948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40374, d355948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40375 q = 1) (hb : d46864 q = 1) : d355949 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40375, d355949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40375, d355949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40201 q = 1) (hb : d46864 q = 1) : d355822 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40201, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40201, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96431 q ha hb
  have h8 (q : Pattern) (ha : d40158 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40158, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96431 q ha hb
    | true =>
      simp only [d40158, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40202 q = 1) (hb : d46864 q = 1) : d355823 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40202, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40202, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40159 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40159, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40159, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40203 q = 1) (hb : d46864 q = 1) : d355824 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40203, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40203, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40204 q = 1) (hb : d46864 q = 1) : d355825 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40204, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40204, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40376 q = 1) (hb : d46864 q = 1) : d355950 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40376, d355950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40376, d355950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d40377 q = 1) (hb : d46864 q = 1) : d355822 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40377, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40377, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96455 q ha hb
  have h15 (q : Pattern) (ha : d40279 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40279, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96455 q ha hb
    | true =>
      simp only [d40279, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40378 q = 1) (hb : d46864 q = 1) : d355823 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40378, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d40378, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40280 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40280, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d40280, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40379 q = 1) (hb : d46864 q = 1) : d355824 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40379, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40379, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40380 q = 1) (hb : d46864 q = 1) : d355825 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40380, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d40380, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d68 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d69 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d40381 q = 1) (hb : d46864 q = 1) : d355826 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40381, d355826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d40381, d355826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d40382 q = 1) (hb : d46864 q = 1) : d355951 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40382, d355951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40382, d355951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro96468 (p : Pattern) (ha : d40388 p = 1) (hb : d46864 p = 1) : d355957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40383 q = 1) (hb : d46864 q = 1) : d355952 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40383, d355952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96467 q ha hb
    | true =>
      simp only [d40383, d355952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96441 q ha hb
  have h2 (q : Pattern) (ha : d40384 q = 1) (hb : d46864 q = 1) : d355953 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40384, d355953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40384, d355953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40385 q = 1) (hb : d46864 q = 1) : d355954 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40385, d355954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40385, d355954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40207 q = 1) (hb : d46864 q = 1) : d355828 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40207, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96441 q ha hb
    | true =>
      simp only [d40207, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96420 q ha hb
  have h5 (q : Pattern) (ha : d40208 q = 1) (hb : d46864 q = 1) : d355829 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40208, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40208, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40209 q = 1) (hb : d46864 q = 1) : d355830 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40209, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40209, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40386 q = 1) (hb : d46864 q = 1) : d355955 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40386, d355955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40386, d355955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96420 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40210 q = 1) (hb : d46864 q = 1) : d355831 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40210, d355831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40210, d355831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40387 q = 1) (hb : d46864 q = 1) : d355956 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40387, d355956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40387, d355956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40388 q = 1) (hb : d46864 q = 1) : d355957 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40388, d355957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40388, d355957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro96469 (p : Pattern) (ha : d40394 p = 1) (hb : d46864 p = 1) : d355963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40389 q = 1) (hb : d46864 q = 1) : d355958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40389, d355958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96468 q ha hb
    | true =>
      simp only [d40389, d355958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40390 q = 1) (hb : d46864 q = 1) : d355959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40390, d355959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40390, d355959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40213 q = 1) (hb : d46864 q = 1) : d355834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40213, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96442 q ha hb
    | true =>
      simp only [d40213, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40214 q = 1) (hb : d46864 q = 1) : d355835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40214, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40214, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40391 q = 1) (hb : d46864 q = 1) : d355960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40391, d355960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40391, d355960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40392 q = 1) (hb : d46864 q = 1) : d355961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40392, d355961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40392, d355961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40393 q = 1) (hb : d46864 q = 1) : d355962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40393, d355962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40393, d355962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40394 q = 1) (hb : d46864 q = 1) : d355963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40394, d355963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40394, d355963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96470 (p : Pattern) (ha : d40419 p = 1) (hb : d46864 p = 1) : d355839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40213 q = 1) (hb : d46864 q = 1) : d355834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40213, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96442 q ha hb
    | true =>
      simp only [d40213, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40214 q = 1) (hb : d46864 q = 1) : d355835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40214, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40214, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40416 q = 1) (hb : d46864 q = 1) : d355836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40416, d355836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40416, d355836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40417 q = 1) (hb : d46864 q = 1) : d355837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40417, d355837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40417, d355837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40418 q = 1) (hb : d46864 q = 1) : d355838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40418, d355838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40418, d355838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40419 q = 1) (hb : d46864 q = 1) : d355839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40419, d355839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40419, d355839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96471 (p : Pattern) (ha : d46864 p = 1) (hb : d289342 p = 1) : d355969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40395 q = 1) (hb : d46864 q = 1) : d355964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40395, d355964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96469 q ha hb
    | true =>
      simp only [d40395, d355964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96443 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d289338 q = 1) : d355965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289338, d355965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289338, d355965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d40420 q = 1) (hb : d46864 q = 1) : d355840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40420, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96470 q ha hb
    | true =>
      simp only [d40420, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40421 q = 1) (hb : d46864 q = 1) : d355841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40421, d355841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40421, d355841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d289339 q = 1) : d355966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289339, d355966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289339, d355966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d289340 q = 1) : d355967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289340, d355967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289340, d355967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d289341 q = 1) : d355968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289341, d355968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289341, d355968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d289342 q = 1) : d355969 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289342, d355969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289342, d355969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96472 (p : Pattern) (ha : d46864 p = 1) (hb : d289348 p = 1) : d355975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40241 q = 1) (hb : d46864 q = 1) : d355862 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40241, d355862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40241, d355862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96448 q ha hb
  have h2 (q : Pattern) (ha : d40242 q = 1) (hb : d46864 q = 1) : d355863 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40242, d355863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40242, d355863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40248 q = 1) (hb : d46864 q = 1) : d355869 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40248, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96448 q ha hb
    | true =>
      simp only [d40248, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96449 q ha hb
  have h4 (q : Pattern) (ha : d40249 q = 1) (hb : d46864 q = 1) : d355870 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40249, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40249, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40250 q = 1) (hb : d46864 q = 1) : d355871 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d40250, d355871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40250, d355871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d289326 q = 1) : d355932 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289326, d355932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96460 q ha hb
    | true =>
      simp only [d289326, d355932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96465 q ha hb
  have h7 (q : Pattern) (ha : d40360 q = 1) (hb : d46864 q = 1) : d355934 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40360, d355934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96450 q ha hb
    | true =>
      simp only [d40360, d355934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96426 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d289327 q = 1) : d355935 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289327, d355935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289327, d355935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d289328 q = 1) : d355936 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289328, d355936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289328, d355936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d289329 q = 1) : d355937 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289329, d355937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d289329, d355937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d289333 q = 1) : d355941 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289333, d355941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289333, d355941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96466 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96446 q ha hb
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d289334 q = 1) : d355942 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289334, d355942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d289334, d355942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d289335 q = 1) : d355943 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289335, d355943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289335, d355943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d289336 q = 1) : d355944 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289336, d355944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d289336, d355944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d46864 q = 1) (hb : d289337 q = 1) : d355945 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289337, d355945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289337, d355945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46864 q = 1) (hb : d289343 q = 1) : d355970 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289343, d355970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289343, d355970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96471 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96447 q ha hb
  have h19 (q : Pattern) (ha : d46864 q = 1) (hb : d289344 q = 1) : d355971 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289344, d355971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289344, d355971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d46864 q = 1) (hb : d289345 q = 1) : d355972 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289345, d355972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d289345, d355972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d46864 q = 1) (hb : d289346 q = 1) : d355973 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289346, d355973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d289346, d355973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d46864 q = 1) (hb : d289347 q = 1) : d355974 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289347, d355974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d289347, d355974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d46864 q = 1) (hb : d289348 q = 1) : d355975 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289348, d355975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289348, d355975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro96473 (p : Pattern) (ha : d46864 p = 1) (hb : d289354 p = 1) : d355981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96424 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d289311 q = 1) : d355852 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289311, d355852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289311, d355852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96445 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d289312 q = 1) : d355853 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289312, d355853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289312, d355853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d289313 q = 1) : d355854 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289313, d355854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289313, d355854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d289314 q = 1) : d355855 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289314, d355855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289314, d355855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d289315 q = 1) : d355856 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289315, d355856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289315, d355856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d289349 q = 1) : d355976 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289349, d355976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289349, d355976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96472 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d289350 q = 1) : d355977 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289350, d355977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289350, d355977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d289351 q = 1) : d355978 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289351, d355978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289351, d355978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d289352 q = 1) : d355979 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289352, d355979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289352, d355979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d289353 q = 1) : d355980 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289353, d355980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289353, d355980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d289354 q = 1) : d355981 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d289354, d355981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289354, d355981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96474 (p : Pattern) (ha : d40440 p = 1) (hb : d46864 p = 1) : d355903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40285 q = 1) (hb : d46864 q = 1) : d355898 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40285, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96456 q ha hb
    | true =>
      simp only [d40285, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96432 q ha hb
  have h2 (q : Pattern) (ha : d40286 q = 1) (hb : d46864 q = 1) : d355899 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40286, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40286, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40287 q = 1) (hb : d46864 q = 1) : d355900 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40287, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40287, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40164 q = 1) (hb : d46864 q = 1) : d355787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40164, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96432 q ha hb
    | true =>
      simp only [d40164, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
  have h5 (q : Pattern) (ha : d40165 q = 1) (hb : d46864 q = 1) : d355788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40165, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40165, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40166 q = 1) (hb : d46864 q = 1) : d355789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40166, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40166, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40288 q = 1) (hb : d46864 q = 1) : d355901 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40288, d355901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40288, d355901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40438 q = 1) (hb : d46864 q = 1) : d355790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40438, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40438, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40439 q = 1) (hb : d46864 q = 1) : d355902 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40439, d355902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40439, d355902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40440 q = 1) (hb : d46864 q = 1) : d355903 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40440, d355903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40440, d355903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro96475 (p : Pattern) (ha : d40444 p = 1) (hb : d46864 p = 1) : d355792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40164 q = 1) (hb : d46864 q = 1) : d355787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40164, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96432 q ha hb
    | true =>
      simp only [d40164, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
  have h2 (q : Pattern) (ha : d40165 q = 1) (hb : d46864 q = 1) : d355788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40165, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40165, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40166 q = 1) (hb : d46864 q = 1) : d355789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40166, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40166, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40438 q = 1) (hb : d46864 q = 1) : d355790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40438, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40438, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40443 q = 1) (hb : d46864 q = 1) : d355791 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40443, d355791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40443, d355791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40444 q = 1) (hb : d46864 q = 1) : d355792 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40444, d355792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40444, d355792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96476 (p : Pattern) (ha : d40450 p = 1) (hb : d46864 p = 1) : d355909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40441 q = 1) (hb : d46864 q = 1) : d355904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96474 q ha hb
    | true =>
      simp only [d40441, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40442 q = 1) (hb : d46864 q = 1) : d355905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40445 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96475 q ha hb
    | true =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40446 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40447 q = 1) (hb : d46864 q = 1) : d355906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40447, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40447, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40448 q = 1) (hb : d46864 q = 1) : d355907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40448, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40448, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40449 q = 1) (hb : d46864 q = 1) : d355908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40449, d355908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40449, d355908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40450 q = 1) (hb : d46864 q = 1) : d355909 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40450, d355909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40450, d355909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96477 (p : Pattern) (ha : d40454 p = 1) (hb : d46864 p = 1) : d355798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40445 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96475 q ha hb
    | true =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40446 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40451 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40451, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40451, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40452 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40452, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40452, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40453 q = 1) (hb : d46864 q = 1) : d355797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40453, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40453, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40454 q = 1) (hb : d46864 q = 1) : d355798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40454, d355798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40454, d355798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96478 (p : Pattern) (ha : d40460 p = 1) (hb : d46864 p = 1) : d355986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40455 q = 1) (hb : d46864 q = 1) : d355910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40455, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96476 q ha hb
    | true =>
      simp only [d40455, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96477 q ha hb
  have h2 (q : Pattern) (ha : d40456 q = 1) (hb : d46864 q = 1) : d355982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40456, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40456, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40457 q = 1) (hb : d46864 q = 1) : d355983 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40457, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40457, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40458 q = 1) (hb : d46864 q = 1) : d355984 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40458, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40458, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40459 q = 1) (hb : d46864 q = 1) : d355985 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40459, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40459, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40460 q = 1) (hb : d46864 q = 1) : d355986 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40460, d355986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40460, d355986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96479 (p : Pattern) (ha : d40463 p = 1) (hb : d46864 p = 1) : d355925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40441 q = 1) (hb : d46864 q = 1) : d355904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96474 q ha hb
    | true =>
      simp only [d40441, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40442 q = 1) (hb : d46864 q = 1) : d355905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40445 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96475 q ha hb
    | true =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40446 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40447 q = 1) (hb : d46864 q = 1) : d355906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40447, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40447, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40448 q = 1) (hb : d46864 q = 1) : d355907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40448, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40448, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40449 q = 1) (hb : d46864 q = 1) : d355908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40449, d355908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40449, d355908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40463 q = 1) (hb : d46864 q = 1) : d355925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40463, d355925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40463, d355925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro96480 (p : Pattern) (ha : d40464 p = 1) (hb : d46864 p = 1) : d355805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40445 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96475 q ha hb
    | true =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40446 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40451 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40451, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40451, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40452 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40452, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40452, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40453 q = 1) (hb : d46864 q = 1) : d355797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40453, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40453, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40464 q = 1) (hb : d46864 q = 1) : d355805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40464, d355805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40464, d355805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96481 (p : Pattern) (ha : d40470 p = 1) (hb : d46864 p = 1) : d355993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40455 q = 1) (hb : d46864 q = 1) : d355910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40455, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96476 q ha hb
    | true =>
      simp only [d40455, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96477 q ha hb
  have h2 (q : Pattern) (ha : d40456 q = 1) (hb : d46864 q = 1) : d355982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40456, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40456, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40457 q = 1) (hb : d46864 q = 1) : d355983 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40457, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40457, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40458 q = 1) (hb : d46864 q = 1) : d355984 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40458, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40458, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40459 q = 1) (hb : d46864 q = 1) : d355985 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40459, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40459, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40465 q = 1) (hb : d46864 q = 1) : d355926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40465, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96479 q ha hb
    | true =>
      simp only [d40465, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96480 q ha hb
  have h7 (q : Pattern) (ha : d40466 q = 1) (hb : d46864 q = 1) : d355989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40466, d355989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40466, d355989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40467 q = 1) (hb : d46864 q = 1) : d355990 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40467, d355990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40467, d355990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40468 q = 1) (hb : d46864 q = 1) : d355991 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40468, d355991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40468, d355991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40469 q = 1) (hb : d46864 q = 1) : d355992 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40469, d355992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40469, d355992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40470 q = 1) (hb : d46864 q = 1) : d355993 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40470, d355993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40470, d355993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96482 (p : Pattern) (ha : d40625 p = 1) (hb : d46864 p = 1) : d356079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40455 q = 1) (hb : d46864 q = 1) : d355910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40455, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96476 q ha hb
    | true =>
      simp only [d40455, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96477 q ha hb
  have h2 (q : Pattern) (ha : d40456 q = 1) (hb : d46864 q = 1) : d355982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40456, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40456, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40457 q = 1) (hb : d46864 q = 1) : d355983 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40457, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40457, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40458 q = 1) (hb : d46864 q = 1) : d355984 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40458, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40458, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40459 q = 1) (hb : d46864 q = 1) : d355985 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40459, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40459, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40620 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40620, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96477 q ha hb
    | true =>
      simp only [d40620, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40621 q = 1) (hb : d46864 q = 1) : d355857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40621, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40621, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40622 q = 1) (hb : d46864 q = 1) : d355858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40622, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40622, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40623 q = 1) (hb : d46864 q = 1) : d355859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40623, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40623, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40624 q = 1) (hb : d46864 q = 1) : d355860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40624, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40624, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40625 q = 1) (hb : d46864 q = 1) : d356079 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40625, d356079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40625, d356079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96483 (p : Pattern) (ha : d40631 p = 1) (hb : d46864 p = 1) : d355868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40620 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40620, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96477 q ha hb
    | true =>
      simp only [d40620, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40621 q = 1) (hb : d46864 q = 1) : d355857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40621, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40621, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40622 q = 1) (hb : d46864 q = 1) : d355858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40622, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40622, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40623 q = 1) (hb : d46864 q = 1) : d355859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40623, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40623, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40624 q = 1) (hb : d46864 q = 1) : d355860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40624, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40624, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40626 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40626, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96480 q ha hb
    | true =>
      simp only [d40626, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40627 q = 1) (hb : d46864 q = 1) : d355864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40627, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40627, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40628 q = 1) (hb : d46864 q = 1) : d355865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40628, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40628, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40629 q = 1) (hb : d46864 q = 1) : d355866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40629, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40629, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40630 q = 1) (hb : d46864 q = 1) : d355867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40630, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40630, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40631 q = 1) (hb : d46864 q = 1) : d355868 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40631, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40631, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96484 (p : Pattern) (ha : d40640 p = 1) (hb : d46864 p = 1) : d356088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40626 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40626, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96480 q ha hb
    | true =>
      simp only [d40626, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40627 q = 1) (hb : d46864 q = 1) : d355864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40627, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40627, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40628 q = 1) (hb : d46864 q = 1) : d355865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40628, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40628, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40629 q = 1) (hb : d46864 q = 1) : d355866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40629, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40629, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40630 q = 1) (hb : d46864 q = 1) : d355867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40630, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40630, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40640 q = 1) (hb : d46864 q = 1) : d356088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40640, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40640, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96485 (p : Pattern) (ha : d40683 p = 1) (hb : d46864 p = 1) : d355833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40207 q = 1) (hb : d46864 q = 1) : d355828 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40207, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96441 q ha hb
    | true =>
      simp only [d40207, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96420 q ha hb
  have h2 (q : Pattern) (ha : d40208 q = 1) (hb : d46864 q = 1) : d355829 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40208, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40208, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40209 q = 1) (hb : d46864 q = 1) : d355830 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40209, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40209, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40673 q = 1) (hb : d46864 q = 1) : d355831 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40673, d355831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40673, d355831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40682 q = 1) (hb : d46864 q = 1) : d355832 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40682, d355832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40682, d355832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40683 q = 1) (hb : d46864 q = 1) : d355833 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40683, d355833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40683, d355833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96486 (p : Pattern) (ha : d40739 p = 1) (hb : d46864 p = 1) : d355839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40684 q = 1) (hb : d46864 q = 1) : d355834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40684, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96485 q ha hb
    | true =>
      simp only [d40684, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40685 q = 1) (hb : d46864 q = 1) : d355835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40685, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40685, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40736 q = 1) (hb : d46864 q = 1) : d355836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40736, d355836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40736, d355836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40737 q = 1) (hb : d46864 q = 1) : d355837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40737, d355837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40737, d355837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40738 q = 1) (hb : d46864 q = 1) : d355838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40738, d355838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40738, d355838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40739 q = 1) (hb : d46864 q = 1) : d355839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40739, d355839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40739, d355839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro96487 (p : Pattern) (ha : d40745 p = 1) (hb : d46864 p = 1) : d356134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40740 q = 1) (hb : d46864 q = 1) : d355840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40740, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96486 q ha hb
    | true =>
      simp only [d40740, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40741 q = 1) (hb : d46864 q = 1) : d356130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40741, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40741, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40742 q = 1) (hb : d46864 q = 1) : d356131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40742, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40742, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40743 q = 1) (hb : d46864 q = 1) : d356132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40743, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40743, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40744 q = 1) (hb : d46864 q = 1) : d356133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40744, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40744, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40745 q = 1) (hb : d46864 q = 1) : d356134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40745, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40745, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96488 (p : Pattern) (ha : d40475 p = 1) (hb : d46864 p = 1) : d355998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40441 q = 1) (hb : d46864 q = 1) : d355904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96474 q ha hb
    | true =>
      simp only [d40441, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40442 q = 1) (hb : d46864 q = 1) : d355905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40445 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96475 q ha hb
    | true =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40446 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40447 q = 1) (hb : d46864 q = 1) : d355906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40447, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40447, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40448 q = 1) (hb : d46864 q = 1) : d355907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40448, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40448, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40474 q = 1) (hb : d46864 q = 1) : d355997 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40474, d355997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40474, d355997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40475 q = 1) (hb : d46864 q = 1) : d355998 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40475, d355998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40475, d355998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96489 (p : Pattern) (ha : d40477 p = 1) (hb : d46864 p = 1) : d355873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40445 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96475 q ha hb
    | true =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40446 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40451 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40451, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40451, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40452 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40452, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40452, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40476 q = 1) (hb : d46864 q = 1) : d355872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40476, d355872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40476, d355872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40477 q = 1) (hb : d46864 q = 1) : d355873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40477, d355873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40477, d355873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96490 (p : Pattern) (ha : d40484 p = 1) (hb : d46864 p = 1) : d356005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40441 q = 1) (hb : d46864 q = 1) : d355904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40441, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96474 q ha hb
    | true =>
      simp only [d40441, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40442 q = 1) (hb : d46864 q = 1) : d355905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40442, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40442, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40445 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96475 q ha hb
    | true =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40446 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40447 q = 1) (hb : d46864 q = 1) : d355906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40447, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40447, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40482 q = 1) (hb : d46864 q = 1) : d356003 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40482, d356003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40482, d356003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40483 q = 1) (hb : d46864 q = 1) : d356004 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40483, d356004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40483, d356004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40484 q = 1) (hb : d46864 q = 1) : d356005 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40484, d356005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40484, d356005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96491 (p : Pattern) (ha : d40487 p = 1) (hb : d46864 p = 1) : d355880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40445 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96475 q ha hb
    | true =>
      simp only [d40445, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40446 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40446, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40451 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40451, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40451, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40485 q = 1) (hb : d46864 q = 1) : d355878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40485, d355878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40485, d355878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40486 q = 1) (hb : d46864 q = 1) : d355879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40486, d355879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40486, d355879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40487 q = 1) (hb : d46864 q = 1) : d355880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40487, d355880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40487, d355880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96492 (p : Pattern) (ha : d40492 p = 1) (hb : d46864 p = 1) : d356010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1997 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1998 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2016 q = 1) (hb : d46864 q = 1) : d46864 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d2017 q = 1) (hb : d46864 q = 1) : d276820 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2017, d276820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2017, d276820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40491 q = 1) (hb : d46864 q = 1) : d356009 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d40491, d356009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40491, d356009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d40149 q = 1) (hb : d46864 q = 1) : d46865 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d40149, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40149, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d40263 q = 1) (hb : d46864 q = 1) : d355884 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d40263, d355884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40263, d355884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d40492 q = 1) (hb : d46864 q = 1) : d356010 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d40492, d356010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40492, d356010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96493 (p : Pattern) (ha : d40497 p = 1) (hb : d46864 p = 1) : d356014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1997 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1997, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2016 q = 1) (hb : d46864 q = 1) : d46864 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d2017 q = 1) (hb : d46864 q = 1) : d276820 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2017, d276820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2017, d276820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2021 q = 1) (hb : d46864 q = 1) : d46865 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2021, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2021, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40496 q = 1) (hb : d46864 q = 1) : d355884 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d40496, d355884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40496, d355884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d308, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1519 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1519, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1531 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h16 (q : Pattern) (ha : d15 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d16 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d9579 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d9579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40497 q = 1) (hb : d46864 q = 1) : d356014 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d40497, d356014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40497, d356014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96494 (p : Pattern) (ha : d40503 p = 1) (hb : d46864 p = 1) : d356020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40493 q = 1) (hb : d46864 q = 1) : d356011 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40493, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96492 q ha hb
    | true =>
      simp only [d40493, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40494 q = 1) (hb : d46864 q = 1) : d356012 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40494, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40494, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40265 q = 1) (hb : d46864 q = 1) : d355886 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96453 q ha hb
    | true =>
      simp only [d40265, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40266 q = 1) (hb : d46864 q = 1) : d355887 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40266, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40495 q = 1) (hb : d46864 q = 1) : d356013 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40495, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40495, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40498 q = 1) (hb : d46864 q = 1) : d356015 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40498, d356015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96493 q ha hb
    | true =>
      simp only [d40498, d356015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40499 q = 1) (hb : d46864 q = 1) : d356016 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40499, d356016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40499, d356016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40152 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96430 q ha hb
    | true =>
      simp only [d40152, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40153 q = 1) (hb : d46864 q = 1) : d355776 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40153, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40500 q = 1) (hb : d46864 q = 1) : d356017 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40500, d356017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40500, d356017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40501 q = 1) (hb : d46864 q = 1) : d356018 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40501, d356018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40501, d356018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d40502 q = 1) (hb : d46864 q = 1) : d356019 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40502, d356019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40502, d356019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40267 q = 1) (hb : d46864 q = 1) : d355888 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40267, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40267, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40154 q = 1) (hb : d46864 q = 1) : d355777 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40154, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40268 q = 1) (hb : d46864 q = 1) : d355889 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40268, d355889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40268, d355889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d40269 q = 1) (hb : d46864 q = 1) : d355890 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40269, d355890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d40269, d355890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d40503 q = 1) (hb : d46864 q = 1) : d356020 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40503, d356020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40503, d356020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96495 (p : Pattern) (ha : d40508 p = 1) (hb : d46864 p = 1) : d355891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40265 q = 1) (hb : d46864 q = 1) : d355886 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96453 q ha hb
    | true =>
      simp only [d40265, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40266 q = 1) (hb : d46864 q = 1) : d355887 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40266, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40152 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96430 q ha hb
    | true =>
      simp only [d40152, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40153 q = 1) (hb : d46864 q = 1) : d355776 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40153, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40267 q = 1) (hb : d46864 q = 1) : d355888 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40267, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40267, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d40154 q = 1) (hb : d46864 q = 1) : d355777 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40154, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d40268 q = 1) (hb : d46864 q = 1) : d355889 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40268, d355889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40268, d355889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40269 q = 1) (hb : d46864 q = 1) : d355890 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40269, d355890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40269, d355890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40276 q = 1) (hb : d46864 q = 1) : d355778 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40276, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d40276, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40277 q = 1) (hb : d46864 q = 1) : d355779 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40277, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40277, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40508 q = 1) (hb : d46864 q = 1) : d355891 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40508, d355891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40508, d355891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro96496 (p : Pattern) (ha : d40516 p = 1) (hb : d46864 p = 1) : d356028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40265 q = 1) (hb : d46864 q = 1) : d355886 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40265, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96453 q ha hb
    | true =>
      simp only [d40265, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40266 q = 1) (hb : d46864 q = 1) : d355887 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40266, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40266, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40152 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d40152, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96430 q ha hb
    | true =>
      simp only [d40152, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40153 q = 1) (hb : d46864 q = 1) : d355776 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d40153, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40153, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40267 q = 1) (hb : d46864 q = 1) : d355888 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40267, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40267, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40514 q = 1) (hb : d46864 q = 1) : d356026 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40514, d356026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40514, d356026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40515 q = 1) (hb : d46864 q = 1) : d356027 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40515, d356027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d40515, d356027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d40154 q = 1) (hb : d46864 q = 1) : d355777 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d40154, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40154, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40276 q = 1) (hb : d46864 q = 1) : d355778 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d40276, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40276, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40277 q = 1) (hb : d46864 q = 1) : d355779 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d40277, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d40277, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d40516 q = 1) (hb : d46864 q = 1) : d356028 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d40516, d356028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40516, d356028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro96497 (p : Pattern) (ha : d40522 p = 1) (hb : d46864 p = 1) : d356034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40504 q = 1) (hb : d46864 q = 1) : d356021 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40504, d356021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96494 q ha hb
    | true =>
      simp only [d40504, d356021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40505 q = 1) (hb : d46864 q = 1) : d356022 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40505, d356022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40505, d356022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40506 q = 1) (hb : d46864 q = 1) : d356023 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40506, d356023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40506, d356023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40507 q = 1) (hb : d46864 q = 1) : d356024 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40507, d356024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40507, d356024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40509 q = 1) (hb : d46864 q = 1) : d355892 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40509, d355892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96495 q ha hb
    | true =>
      simp only [d40509, d355892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40510 q = 1) (hb : d46864 q = 1) : d355893 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40510, d355893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40510, d355893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d40511 q = 1) (hb : d46864 q = 1) : d355894 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40511, d355894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40511, d355894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40512 q = 1) (hb : d46864 q = 1) : d355895 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40512, d355895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40512, d355895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40513 q = 1) (hb : d46864 q = 1) : d356025 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40513, d356025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40513, d356025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40517 q = 1) (hb : d46864 q = 1) : d356029 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40517, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96496 q ha hb
    | true =>
      simp only [d40517, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40518 q = 1) (hb : d46864 q = 1) : d356030 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40518, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40518, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d40519 q = 1) (hb : d46864 q = 1) : d356031 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40519, d356031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40519, d356031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40520 q = 1) (hb : d46864 q = 1) : d356032 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40520, d356032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d40520, d356032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d40279 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40279, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96455 q ha hb
    | true =>
      simp only [d40279, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d40280 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40280, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d40280, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d40281 q = 1) (hb : d46864 q = 1) : d355783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40281, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40281, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d40282 q = 1) (hb : d46864 q = 1) : d355784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40282, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d40282, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d40521 q = 1) (hb : d46864 q = 1) : d356033 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40521, d356033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d40521, d356033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d40522 q = 1) (hb : d46864 q = 1) : d356034 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40522, d356034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40522, d356034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96498 (p : Pattern) (ha : d40526 p = 1) (hb : d46864 p = 1) : d355786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40279 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d40279, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96455 q ha hb
    | true =>
      simp only [d40279, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40280 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d40280, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40280, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d40281 q = 1) (hb : d46864 q = 1) : d355783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d40281, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40281, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40282 q = 1) (hb : d46864 q = 1) : d355784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d40282, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40282, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d40283 q = 1) (hb : d46864 q = 1) : d355785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d40283, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40283, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d40526 q = 1) (hb : d46864 q = 1) : d355786 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d40526, d355786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d40526, d355786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96499 (p : Pattern) (ha : d40532 p = 1) (hb : d46864 p = 1) : d356040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40523 q = 1) (hb : d46864 q = 1) : d356035 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40523, d356035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96497 q ha hb
    | true =>
      simp only [d40523, d356035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96456 q ha hb
  have h2 (q : Pattern) (ha : d40524 q = 1) (hb : d46864 q = 1) : d356036 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40524, d356036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40524, d356036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40525 q = 1) (hb : d46864 q = 1) : d356037 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40525, d356037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40525, d356037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40527 q = 1) (hb : d46864 q = 1) : d355898 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40527, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96456 q ha hb
    | true =>
      simp only [d40527, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96498 q ha hb
  have h5 (q : Pattern) (ha : d40528 q = 1) (hb : d46864 q = 1) : d355899 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40528, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40528, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40529 q = 1) (hb : d46864 q = 1) : d355900 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40529, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40529, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d40530 q = 1) (hb : d46864 q = 1) : d356038 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40530, d356038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40530, d356038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d40285 q = 1) (hb : d46864 q = 1) : d355898 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40285, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96456 q ha hb
    | true =>
      simp only [d40285, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96432 q ha hb
  have h9 (q : Pattern) (ha : d40286 q = 1) (hb : d46864 q = 1) : d355899 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40286, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40286, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d40287 q = 1) (hb : d46864 q = 1) : d355900 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40287, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40287, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d40164 q = 1) (hb : d46864 q = 1) : d355787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d40164, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96432 q ha hb
    | true =>
      simp only [d40164, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
  have h12 (q : Pattern) (ha : d40165 q = 1) (hb : d46864 q = 1) : d355788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d40165, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40165, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d40166 q = 1) (hb : d46864 q = 1) : d355789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d40166, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40166, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d40288 q = 1) (hb : d46864 q = 1) : d355901 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d40288, d355901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d40288, d355901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d40531 q = 1) (hb : d46864 q = 1) : d356039 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d40531, d356039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d40531, d356039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d40532 q = 1) (hb : d46864 q = 1) : d356040 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d40532, d356040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d40532, d356040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
end NetHack.Soko22Hazard87
