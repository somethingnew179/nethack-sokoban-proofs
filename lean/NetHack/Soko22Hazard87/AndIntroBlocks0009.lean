import NetHack.Soko22Hazard87.AndIntroBlocks0008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro2250 (p : Pattern) (ha : d521 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d520 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d521 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d521, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d521, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2251 (p : Pattern) (ha : d524 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d523 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d524 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2252 (p : Pattern) (ha : d560 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d559 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d560 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d560, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d560, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2253 (p : Pattern) (ha : d51685 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d515 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2248 q ha hb
    | true =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2249 q ha hb
  have h3 (q : Pattern) (ha : d516 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d517 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d518 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d525 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2250 q ha hb
    | true =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2251 q ha hb
  have h7 (q : Pattern) (ha : d526 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d527 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d561 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2252 q ha hb
    | true =>
      simp only [d561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2242 q ha hb
  have h10 (q : Pattern) (ha : d4408 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d603 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2242 q ha hb
    | true =>
      simp only [d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d604 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d4409 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51683 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51684 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51685 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51685, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51685, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro2254 (p : Pattern) (ha : d51688 p = 1) (hb : d62938 p = 1) : d63658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51687 q = 1) (hb : d62936 q = 1) : d51687 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51688 q = 1) (hb : d62938 q = 1) : d63658 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51688, d62938, d63658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51688, d62938, d63658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2255 (p : Pattern) (ha : d54767 p = 1) (hb : d62939 p = 1) : d63664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2244 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d62938 q = 1) : d53681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2244 q ha hb
    | true =>
      simp only [d508, d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2245 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d62938 q = 1) : d53682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d62938 q = 1) : d63657 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d63657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d63657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51689 q = 1) (hb : d62938 q = 1) : d63659 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d63659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2253 q ha hb
    | true =>
      simp only [d51689, d63659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2254 q ha hb
  have h7 (q : Pattern) (ha : d645 q = 1) (hb : d62938 q = 1) : d654 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2246 q ha hb
    | true =>
      simp only [d645, d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2247 q ha hb
  have h8 (q : Pattern) (ha : d51690 q = 1) (hb : d62938 q = 1) : d63660 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d63660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51690, d63660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51691 q = 1) (hb : d62938 q = 1) : d63661 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d63661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51691, d63661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51692 q = 1) (hb : d62938 q = 1) : d63662 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d63662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51692, d63662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54766 q = 1) (hb : d62939 q = 1) : d63663 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54766, d62939, d63663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54766, d62939, d63663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54767 q = 1) (hb : d62939 q = 1) : d63664 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54767, d63664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54767, d63664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2256 (p : Pattern) (ha : d54773 p = 1) (hb : d62939 p = 1) : d63670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54768 q = 1) (hb : d62939 q = 1) : d63665 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54768, d63665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54768, d63665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2255 q ha hb
  have h2 (q : Pattern) (ha : d54769 q = 1) (hb : d62939 q = 1) : d63666 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54769, d63666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54769, d63666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54770 q = 1) (hb : d62939 q = 1) : d63667 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54770, d63667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54770, d63667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54771 q = 1) (hb : d62939 q = 1) : d63668 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54771, d63668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54771, d63668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54772 q = 1) (hb : d62939 q = 1) : d63669 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54772, d63669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54772, d63669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54773 q = 1) (hb : d62939 q = 1) : d63670 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54773, d63670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54773, d63670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2257 (p : Pattern) (ha : d779 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d778 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d779 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d779, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d779, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2258 (p : Pattern) (ha : d783 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d782 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d783 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2259 (p : Pattern) (ha : d789 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d784 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2257 q ha hb
    | true =>
      simp only [d784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2258 q ha hb
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d786 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d787 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d788 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d789 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2260 (p : Pattern) (ha : d799 p = 1) (hb : d62938 p = 1) : d53707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d788 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d798 q = 1) (hb : d62936 q = 1) : d798 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d799 q = 1) (hb : d62938 q = 1) : d53707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, d62938, d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d799, d62938, d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2261 (p : Pattern) (ha : d944 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d788 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d939 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2258 q ha hb
    | true =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d940 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d941 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d942 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d943 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d944 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d944, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d944, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2262 (p : Pattern) (ha : d950 p = 1) (hb : d62938 p = 1) : d959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d943 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d949 q = 1) (hb : d62936 q = 1) : d949 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d950 q = 1) (hb : d62938 q = 1) : d959 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d62938, d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d950, d62938, d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2263 (p : Pattern) (ha : d804 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d803 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d804 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d804, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d804, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2264 (p : Pattern) (ha : d806 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d805 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d806 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2265 (p : Pattern) (ha : d813 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d812 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d813 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d813, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d813, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2266 (p : Pattern) (ha : d816 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d816 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2267 (p : Pattern) (ha : d851 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d850 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d851 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d851, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d851, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2268 (p : Pattern) (ha : d51711 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d807 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2263 q ha hb
    | true =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2264 q ha hb
  have h3 (q : Pattern) (ha : d808 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d809 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d810 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d817 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2265 q ha hb
    | true =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2266 q ha hb
  have h7 (q : Pattern) (ha : d818 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d819 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d852 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2267 q ha hb
    | true =>
      simp only [d852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2257 q ha hb
  have h10 (q : Pattern) (ha : d4446 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d909 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2257 q ha hb
    | true =>
      simp only [d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d910 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d4447 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51709 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51710 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51711 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51711, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51711, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro2269 (p : Pattern) (ha : d51714 p = 1) (hb : d62938 p = 1) : d63673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51713 q = 1) (hb : d62936 q = 1) : d51713 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51714 q = 1) (hb : d62938 q = 1) : d63673 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51714, d62938, d63673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51714, d62938, d63673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2270 (p : Pattern) (ha : d54776 p = 1) (hb : d62939 p = 1) : d63679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2259 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d62938 q = 1) : d53708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2259 q ha hb
    | true =>
      simp only [d800, d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2260 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d62938 q = 1) : d53709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d62938 q = 1) : d63672 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d63672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d63672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51715 q = 1) (hb : d62938 q = 1) : d63674 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d63674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2268 q ha hb
    | true =>
      simp only [d51715, d63674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2269 q ha hb
  have h7 (q : Pattern) (ha : d951 q = 1) (hb : d62938 q = 1) : d960 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2261 q ha hb
    | true =>
      simp only [d951, d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2262 q ha hb
  have h8 (q : Pattern) (ha : d51716 q = 1) (hb : d62938 q = 1) : d63675 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d63675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51716, d63675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51717 q = 1) (hb : d62938 q = 1) : d63676 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d63676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51717, d63676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51718 q = 1) (hb : d62938 q = 1) : d63677 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d63677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51718, d63677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54775 q = 1) (hb : d62939 q = 1) : d63678 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54775, d62939, d63678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54775, d62939, d63678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54776 q = 1) (hb : d62939 q = 1) : d63679 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54776, d63679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54776, d63679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2271 (p : Pattern) (ha : d54782 p = 1) (hb : d62939 p = 1) : d63685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54777 q = 1) (hb : d62939 q = 1) : d63680 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54777, d63680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54777, d63680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2270 q ha hb
  have h2 (q : Pattern) (ha : d54778 q = 1) (hb : d62939 q = 1) : d63681 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54778, d63681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54778, d63681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54779 q = 1) (hb : d62939 q = 1) : d63682 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54779, d63682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54779, d63682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54780 q = 1) (hb : d62939 q = 1) : d63683 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54780, d63683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54780, d63683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54781 q = 1) (hb : d62939 q = 1) : d63684 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54781, d63684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54781, d63684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54782 q = 1) (hb : d62939 q = 1) : d63685 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54782, d63685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54782, d63685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2272 (p : Pattern) (ha : d1158 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1157 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1158 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1158, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1158, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2273 (p : Pattern) (ha : d1162 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1161 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1162 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2274 (p : Pattern) (ha : d1168 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1163 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2272 q ha hb
    | true =>
      simp only [d1163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2273 q ha hb
  have h3 (q : Pattern) (ha : d1164 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1165 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1166 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1167 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1168 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2275 (p : Pattern) (ha : d1178 p = 1) (hb : d62938 p = 1) : d53735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1177 q = 1) (hb : d62936 q = 1) : d1177 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1178 q = 1) (hb : d62938 q = 1) : d53735 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, d62938, d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1178, d62938, d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2276 (p : Pattern) (ha : d1355 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1350 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2273 q ha hb
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1351 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1352 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1353 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1354 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1355 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1355, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1355, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2277 (p : Pattern) (ha : d1361 p = 1) (hb : d62938 p = 1) : d1370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1354 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1360 q = 1) (hb : d62936 q = 1) : d1360 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1361 q = 1) (hb : d62938 q = 1) : d1370 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, d62938, d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1361, d62938, d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2278 (p : Pattern) (ha : d1183 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1182 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1183 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1183, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1183, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2279 (p : Pattern) (ha : d1185 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1184 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1185 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2280 (p : Pattern) (ha : d1192 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1191 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1192 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1192, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1192, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2281 (p : Pattern) (ha : d1195 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1194 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1195 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2282 (p : Pattern) (ha : d1227 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1226 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1227 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1227, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1227, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2283 (p : Pattern) (ha : d51738 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1186 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2278 q ha hb
    | true =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2279 q ha hb
  have h3 (q : Pattern) (ha : d1187 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1188 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1189 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1196 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2280 q ha hb
    | true =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2281 q ha hb
  have h7 (q : Pattern) (ha : d1197 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1198 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1228 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2282 q ha hb
    | true =>
      simp only [d1228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2272 q ha hb
  have h10 (q : Pattern) (ha : d4485 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1320 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2272 q ha hb
    | true =>
      simp only [d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1321 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d4486 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51736 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51737 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51738 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51738, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51738, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro2284 (p : Pattern) (ha : d51741 p = 1) (hb : d62938 p = 1) : d63689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51740 q = 1) (hb : d62936 q = 1) : d51740 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51741 q = 1) (hb : d62938 q = 1) : d63689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51741, d62938, d63689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51741, d62938, d63689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2285 (p : Pattern) (ha : d54786 p = 1) (hb : d62939 p = 1) : d63695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2274 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d62938 q = 1) : d53736 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2274 q ha hb
    | true =>
      simp only [d1179, d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2275 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d62938 q = 1) : d53737 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d62938 q = 1) : d63688 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d63688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d63688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51742 q = 1) (hb : d62938 q = 1) : d63690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d63690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2283 q ha hb
    | true =>
      simp only [d51742, d63690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2284 q ha hb
  have h7 (q : Pattern) (ha : d1362 q = 1) (hb : d62938 q = 1) : d1371 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2276 q ha hb
    | true =>
      simp only [d1362, d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2277 q ha hb
  have h8 (q : Pattern) (ha : d51743 q = 1) (hb : d62938 q = 1) : d63691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d63691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51743, d63691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51744 q = 1) (hb : d62938 q = 1) : d63692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d63692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51744, d63692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51745 q = 1) (hb : d62938 q = 1) : d63693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d63693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51745, d63693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54785 q = 1) (hb : d62939 q = 1) : d63694 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54785, d62939, d63694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54785, d62939, d63694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54786 q = 1) (hb : d62939 q = 1) : d63695 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54786, d63695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54786, d63695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2286 (p : Pattern) (ha : d54792 p = 1) (hb : d62939 p = 1) : d63701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54787 q = 1) (hb : d62939 q = 1) : d63696 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54787, d63696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54787, d63696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2285 q ha hb
  have h2 (q : Pattern) (ha : d54788 q = 1) (hb : d62939 q = 1) : d63697 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54788, d63697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54788, d63697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54789 q = 1) (hb : d62939 q = 1) : d63698 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54789, d63698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54789, d63698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54790 q = 1) (hb : d62939 q = 1) : d63699 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54790, d63699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54790, d63699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54791 q = 1) (hb : d62939 q = 1) : d63700 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54791, d63700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54791, d63700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54792 q = 1) (hb : d62939 q = 1) : d63701 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54792, d63701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54792, d63701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2287 (p : Pattern) (ha : d1619 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1618 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1619 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1619, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1619, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2288 (p : Pattern) (ha : d1623 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1622 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1623 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2289 (p : Pattern) (ha : d1629 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1624 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2287 q ha hb
    | true =>
      simp only [d1624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2288 q ha hb
  have h3 (q : Pattern) (ha : d1625 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1626 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1627 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1628 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1629 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2290 (p : Pattern) (ha : d1639 p = 1) (hb : d62938 p = 1) : d53764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1628 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1638 q = 1) (hb : d62936 q = 1) : d1638 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1639 q = 1) (hb : d62938 q = 1) : d53764 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d62938, d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1639, d62938, d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2291 (p : Pattern) (ha : d1832 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1628 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1827 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2288 q ha hb
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1828 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1829 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1830 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1831 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1832 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1832, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1832, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2292 (p : Pattern) (ha : d1838 p = 1) (hb : d62938 p = 1) : d1847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1831 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1837 q = 1) (hb : d62936 q = 1) : d1837 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1838 q = 1) (hb : d62938 q = 1) : d1847 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, d62938, d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1838, d62938, d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2293 (p : Pattern) (ha : d1644 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1643 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1644 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1644, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1644, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2294 (p : Pattern) (ha : d1646 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1645 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1646 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2295 (p : Pattern) (ha : d1653 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1653 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1653, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1653, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2296 (p : Pattern) (ha : d1656 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1655 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1656 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2297 (p : Pattern) (ha : d1682 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1681 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1682 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1682, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1682, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2298 (p : Pattern) (ha : d51766 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1647 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2293 q ha hb
    | true =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2294 q ha hb
  have h3 (q : Pattern) (ha : d1648 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1649 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1650 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1657 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2295 q ha hb
    | true =>
      simp only [d1657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2296 q ha hb
  have h7 (q : Pattern) (ha : d1658 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1659 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1683 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2297 q ha hb
    | true =>
      simp only [d1683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2287 q ha hb
  have h10 (q : Pattern) (ha : d4525 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1797 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2287 q ha hb
    | true =>
      simp only [d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1798 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d4526 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51764 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51765 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51766 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51766, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51766, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro2299 (p : Pattern) (ha : d51769 p = 1) (hb : d62938 p = 1) : d63706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51765 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51768 q = 1) (hb : d62936 q = 1) : d51768 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51769 q = 1) (hb : d62938 q = 1) : d63706 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51769, d62938, d63706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51769, d62938, d63706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2300 (p : Pattern) (ha : d54797 p = 1) (hb : d62939 p = 1) : d63712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2289 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d62938 q = 1) : d53765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2289 q ha hb
    | true =>
      simp only [d1640, d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2290 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d62938 q = 1) : d53766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d62938 q = 1) : d63705 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d63705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d63705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51770 q = 1) (hb : d62938 q = 1) : d63707 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d63707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2298 q ha hb
    | true =>
      simp only [d51770, d63707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2299 q ha hb
  have h7 (q : Pattern) (ha : d1839 q = 1) (hb : d62938 q = 1) : d1848 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2291 q ha hb
    | true =>
      simp only [d1839, d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2292 q ha hb
  have h8 (q : Pattern) (ha : d51771 q = 1) (hb : d62938 q = 1) : d63708 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d63708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51771, d63708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51772 q = 1) (hb : d62938 q = 1) : d63709 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d63709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51772, d63709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51773 q = 1) (hb : d62938 q = 1) : d63710 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d63710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51773, d63710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54796 q = 1) (hb : d62939 q = 1) : d63711 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54796, d62939, d63711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54796, d62939, d63711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54797 q = 1) (hb : d62939 q = 1) : d63712 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54797, d63712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54797, d63712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2301 (p : Pattern) (ha : d54803 p = 1) (hb : d62939 p = 1) : d63718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54798 q = 1) (hb : d62939 q = 1) : d63713 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54798, d63713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54798, d63713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2300 q ha hb
  have h2 (q : Pattern) (ha : d54799 q = 1) (hb : d62939 q = 1) : d63714 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54799, d63714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54799, d63714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54800 q = 1) (hb : d62939 q = 1) : d63715 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54800, d63715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54800, d63715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54801 q = 1) (hb : d62939 q = 1) : d63716 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54801, d63716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54801, d63716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54802 q = 1) (hb : d62939 q = 1) : d63717 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54802, d63717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54802, d63717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54803 q = 1) (hb : d62939 q = 1) : d63718 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54803, d63718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54803, d63718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2302 (p : Pattern) (ha : d2102 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2101 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2102 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2102, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2102, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2303 (p : Pattern) (ha : d2106 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2106 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2304 (p : Pattern) (ha : d2112 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2107 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2302 q ha hb
    | true =>
      simp only [d2107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2303 q ha hb
  have h3 (q : Pattern) (ha : d2108 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2109 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2110 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2111 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2112 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2305 (p : Pattern) (ha : d2122 p = 1) (hb : d62938 p = 1) : d53794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2111 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2121 q = 1) (hb : d62936 q = 1) : d2121 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2122 q = 1) (hb : d62938 q = 1) : d53794 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, d62938, d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2122, d62938, d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2306 (p : Pattern) (ha : d2310 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2111 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2305 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2303 q ha hb
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2306 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2307 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2308 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2309 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2310 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2310, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2310, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2307 (p : Pattern) (ha : d2316 p = 1) (hb : d62938 p = 1) : d2325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2309 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2315 q = 1) (hb : d62936 q = 1) : d2315 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2316 q = 1) (hb : d62938 q = 1) : d2325 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, d62938, d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2316, d62938, d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2308 (p : Pattern) (ha : d2127 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2127 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2127, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2127, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2309 (p : Pattern) (ha : d2129 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2128 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2129 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2310 (p : Pattern) (ha : d2136 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2135 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2136 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2136, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2136, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2311 (p : Pattern) (ha : d2139 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2138 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2139 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2312 (p : Pattern) (ha : d2161 p = 1) (hb : d62936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2160 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2161 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2161, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2161, d62936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro2313 (p : Pattern) (ha : d51795 p = 1) (hb : d62938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2130 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2308 q ha hb
    | true =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2309 q ha hb
  have h3 (q : Pattern) (ha : d2131 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2132 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2133 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2140 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2310 q ha hb
    | true =>
      simp only [d2140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2311 q ha hb
  have h7 (q : Pattern) (ha : d2141 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2142 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2162 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2312 q ha hb
    | true =>
      simp only [d2162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2302 q ha hb
  have h10 (q : Pattern) (ha : d4566 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2275 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2302 q ha hb
    | true =>
      simp only [d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d2276 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d4567 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51793 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51794 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51795 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51795, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51795, d62938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro2314 (p : Pattern) (ha : d51798 p = 1) (hb : d62938 p = 1) : d63724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51797 q = 1) (hb : d62936 q = 1) : d51797 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51798 q = 1) (hb : d62938 q = 1) : d63724 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51798, d62938, d63724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51798, d62938, d63724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro2315 (p : Pattern) (ha : d54809 p = 1) (hb : d62939 p = 1) : d63730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2304 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d62938 q = 1) : d53795 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2304 q ha hb
    | true =>
      simp only [d2123, d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2305 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d62938 q = 1) : d53796 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d62938 q = 1) : d63723 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d63723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d63723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51799 q = 1) (hb : d62938 q = 1) : d63725 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d63725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2313 q ha hb
    | true =>
      simp only [d51799, d63725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2314 q ha hb
  have h7 (q : Pattern) (ha : d2317 q = 1) (hb : d62938 q = 1) : d2326 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2306 q ha hb
    | true =>
      simp only [d2317, d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2307 q ha hb
  have h8 (q : Pattern) (ha : d51800 q = 1) (hb : d62938 q = 1) : d63726 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d63726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51800, d63726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51801 q = 1) (hb : d62938 q = 1) : d63727 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d63727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51801, d63727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51802 q = 1) (hb : d62938 q = 1) : d63728 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d63728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51802, d63728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d54808 q = 1) (hb : d62939 q = 1) : d63729 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54808, d62939, d63729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54808, d62939, d63729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d54809 q = 1) (hb : d62939 q = 1) : d63730 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54809, d63730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54809, d63730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro2316 (p : Pattern) (ha : d54815 p = 1) (hb : d62939 p = 1) : d63736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54810 q = 1) (hb : d62939 q = 1) : d63731 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54810, d63731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54810, d63731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2315 q ha hb
  have h2 (q : Pattern) (ha : d54811 q = 1) (hb : d62939 q = 1) : d63732 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54811, d63732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54811, d63732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54812 q = 1) (hb : d62939 q = 1) : d63733 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54812, d63733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54812, d63733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54813 q = 1) (hb : d62939 q = 1) : d63734 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54813, d63734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54813, d63734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54814 q = 1) (hb : d62939 q = 1) : d63735 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54814, d63735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54814, d63735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54815 q = 1) (hb : d62939 q = 1) : d63736 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54815, d63736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54815, d63736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2317 (p : Pattern) (ha : d54821 p = 1) (hb : d62939 p = 1) : d63742 p = 1 := by
  have h0 (q : Pattern) (ha : d54774 q = 1) (hb : d62939 q = 1) : d63671 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54774, d63671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2241 q ha hb
    | true =>
      simp only [d54774, d63671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2256 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54783 q = 1) (hb : d62939 q = 1) : d63686 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54783, d63686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54783, d63686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2271 q ha hb
  have h3 (q : Pattern) (ha : d54784 q = 1) (hb : d62939 q = 1) : d63687 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54784, d63687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54784, d63687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54793 q = 1) (hb : d62939 q = 1) : d63702 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54793, d63702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54793, d63702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2286 q ha hb
  have h5 (q : Pattern) (ha : d54794 q = 1) (hb : d62939 q = 1) : d63703 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54794, d63703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54794, d63703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54795 q = 1) (hb : d62939 q = 1) : d63704 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54795, d63704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54795, d63704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54804 q = 1) (hb : d62939 q = 1) : d63719 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54804, d63719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54804, d63719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2301 q ha hb
  have h8 (q : Pattern) (ha : d54805 q = 1) (hb : d62939 q = 1) : d63720 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54805, d63720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54805, d63720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54806 q = 1) (hb : d62939 q = 1) : d63721 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54806, d63721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54806, d63721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54807 q = 1) (hb : d62939 q = 1) : d63722 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54807, d63722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54807, d63722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54816 q = 1) (hb : d62939 q = 1) : d63737 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54816, d63737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54816, d63737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2316 q ha hb
  have h12 (q : Pattern) (ha : d54817 q = 1) (hb : d62939 q = 1) : d63738 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54817, d63738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54817, d63738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54818 q = 1) (hb : d62939 q = 1) : d63739 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54818, d63739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54818, d63739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54819 q = 1) (hb : d62939 q = 1) : d63740 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54819, d63740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54819, d63740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54820 q = 1) (hb : d62939 q = 1) : d63741 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54820, d63741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54820, d63741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54821 q = 1) (hb : d62939 q = 1) : d63742 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54821, d63742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54821, d63742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2318 (p : Pattern) (ha : d54827 p = 1) (hb : d62939 p = 1) : d63748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54822 q = 1) (hb : d62939 q = 1) : d63743 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54822, d63743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2317 q ha hb
    | true =>
      simp only [d54822, d63743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54823 q = 1) (hb : d62939 q = 1) : d63744 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54823, d63744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54823, d63744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54824 q = 1) (hb : d62939 q = 1) : d63745 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54824, d63745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54824, d63745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54825 q = 1) (hb : d62939 q = 1) : d63746 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54825, d63746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54825, d63746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54826 q = 1) (hb : d62939 q = 1) : d63747 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54826, d63747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54826, d63747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54827 q = 1) (hb : d62939 q = 1) : d63748 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54827, d63748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54827, d63748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2319 (p : Pattern) (ha : d54833 p = 1) (hb : d62939 p = 1) : d63754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54828 q = 1) (hb : d62939 q = 1) : d63749 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54828, d63749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2318 q ha hb
    | true =>
      simp only [d54828, d63749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54829 q = 1) (hb : d62939 q = 1) : d63750 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54829, d63750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54829, d63750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54830 q = 1) (hb : d62939 q = 1) : d63751 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54830, d63751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54830, d63751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54831 q = 1) (hb : d62939 q = 1) : d63752 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54831, d63752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54831, d63752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54832 q = 1) (hb : d62939 q = 1) : d63753 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54832, d63753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54832, d63753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54833 q = 1) (hb : d62939 q = 1) : d63754 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54833, d63754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54833, d63754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2320 (p : Pattern) (ha : d54839 p = 1) (hb : d62939 p = 1) : d63760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54834 q = 1) (hb : d62939 q = 1) : d63755 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54834, d63755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2319 q ha hb
    | true =>
      simp only [d54834, d63755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54835 q = 1) (hb : d62939 q = 1) : d63756 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54835, d63756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54835, d63756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54836 q = 1) (hb : d62939 q = 1) : d63757 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54836, d63757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54836, d63757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54837 q = 1) (hb : d62939 q = 1) : d63758 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54837, d63758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54837, d63758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54838 q = 1) (hb : d62939 q = 1) : d63759 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54838, d63759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54838, d63759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54839 q = 1) (hb : d62939 q = 1) : d63760 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54839, d63760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54839, d63760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2321 (p : Pattern) (ha : d54845 p = 1) (hb : d62939 p = 1) : d63766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54840 q = 1) (hb : d62939 q = 1) : d63761 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54840, d63761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2320 q ha hb
    | true =>
      simp only [d54840, d63761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54841 q = 1) (hb : d62939 q = 1) : d63762 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54841, d63762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54841, d63762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54842 q = 1) (hb : d62939 q = 1) : d63763 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54842, d63763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54842, d63763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54843 q = 1) (hb : d62939 q = 1) : d63764 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54843, d63764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54843, d63764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54844 q = 1) (hb : d62939 q = 1) : d63765 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54844, d63765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54844, d63765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54845 q = 1) (hb : d62939 q = 1) : d63766 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54845, d63766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54845, d63766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2322 (p : Pattern) (ha : d54851 p = 1) (hb : d62939 p = 1) : d63772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54846 q = 1) (hb : d62939 q = 1) : d63767 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54846, d63767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2321 q ha hb
    | true =>
      simp only [d54846, d63767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54847 q = 1) (hb : d62939 q = 1) : d63768 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54847, d63768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54847, d63768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54848 q = 1) (hb : d62939 q = 1) : d63769 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54848, d63769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54848, d63769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54849 q = 1) (hb : d62939 q = 1) : d63770 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54849, d63770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54849, d63770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54850 q = 1) (hb : d62939 q = 1) : d63771 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54850, d63771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54850, d63771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54851 q = 1) (hb : d62939 q = 1) : d63772 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54851, d63772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54851, d63772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2323 (p : Pattern) (ha : d54857 p = 1) (hb : d62939 p = 1) : d63778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54852 q = 1) (hb : d62939 q = 1) : d63773 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54852, d63773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2322 q ha hb
    | true =>
      simp only [d54852, d63773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54853 q = 1) (hb : d62939 q = 1) : d63774 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54853, d63774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54853, d63774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54854 q = 1) (hb : d62939 q = 1) : d63775 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54854, d63775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54854, d63775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54855 q = 1) (hb : d62939 q = 1) : d63776 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54855, d63776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54855, d63776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54856 q = 1) (hb : d62939 q = 1) : d63777 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54856, d63777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54856, d63777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54857 q = 1) (hb : d62939 q = 1) : d63778 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54857, d63778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54857, d63778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2324 (p : Pattern) (ha : d54863 p = 1) (hb : d62939 p = 1) : d63784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54858 q = 1) (hb : d62939 q = 1) : d63779 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54858, d63779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2323 q ha hb
    | true =>
      simp only [d54858, d63779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54859 q = 1) (hb : d62939 q = 1) : d63780 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54859, d63780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54859, d63780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54860 q = 1) (hb : d62939 q = 1) : d63781 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54860, d63781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54860, d63781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54861 q = 1) (hb : d62939 q = 1) : d63782 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54861, d63782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54861, d63782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54862 q = 1) (hb : d62939 q = 1) : d63783 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54862, d63783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54862, d63783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54863 q = 1) (hb : d62939 q = 1) : d63784 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54863, d63784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54863, d63784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2325 (p : Pattern) (ha : d49 p = 1) (hb : d51893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d51891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d51892 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, d51892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, d51892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d51893 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, d51893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, d51893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51893 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d51893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2326 (p : Pattern) (ha : d60 p = 1) (hb : d63289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63289 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d63285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d63285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2325 q ha hb
    | true =>
      simp only [d50, d63285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51 q = 1) (hb : d63286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d63286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51, d63286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d52 q = 1) (hb : d63287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, d63287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52, d63287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d53 q = 1) (hb : d63288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, d63288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53, d63288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54 q = 1) (hb : d63289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, d63289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54, d63289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60 q = 1) (hb : d63289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2327 (p : Pattern) (ha : d63295 p = 1) (hb : d63625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61 q = 1) (hb : d63290 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, d63290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, d63290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2326 q ha hb
  have h2 (q : Pattern) (ha : d62 q = 1) (hb : d63291 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, d63291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62, d63291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63 q = 1) (hb : d63292 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, d63292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63, d63292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d63293 q = 1) (hb : d63623 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63293, d63623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63293, d63623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d63294 q = 1) (hb : d63624 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63294, d63624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63294, d63624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63295 q = 1) (hb : d63625 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63295, d63625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63295, d63625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2328 (p : Pattern) (ha : d406 p = 1) (hb : d63303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63303 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d63285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d63285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2325 q ha hb
    | true =>
      simp only [d50, d63285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d63300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d63300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d63300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108 q = 1) (hb : d63301 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d63301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d63301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d109 q = 1) (hb : d63302 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d63302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109, d63302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d110 q = 1) (hb : d63303 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d63303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d110, d63303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d406 q = 1) (hb : d63303 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2329 (p : Pattern) (ha : d194 p = 1) (hb : d51967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d51891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d51892 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, d51892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, d51892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d51967 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, d51967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, d51967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51967 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d194 q = 1) (hb : d51967 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2330 (p : Pattern) (ha : d199 p = 1) (hb : d51974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d51891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d51973 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, d51973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, d51973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d51974 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, d51974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, d51974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51974 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199 q = 1) (hb : d51974 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2331 (p : Pattern) (ha : d203 p = 1) (hb : d52006 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d155 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d203 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2332 (p : Pattern) (ha : d63318 p = 1) (hb : d63631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63318 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d195 q = 1) (hb : d63307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d63307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2329 q ha hb
    | true =>
      simp only [d195, d63307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d196 q = 1) (hb : d63308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d63308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196, d63308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d197 q = 1) (hb : d63309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d63309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197, d63309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d198 q = 1) (hb : d63310 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d63310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d198, d63310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200 q = 1) (hb : d63311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d63311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2330 q ha hb
    | true =>
      simp only [d200, d63311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d201 q = 1) (hb : d63312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d63312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201, d63312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202 q = 1) (hb : d63313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d63313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202, d63313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d204 q = 1) (hb : d63314 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d63314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2331 q ha hb
    | true =>
      simp only [d204, d63314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2325 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d63285 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4340 q = 1) (hb : d63315 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d63315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4340, d63315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d50 q = 1) (hb : d63285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d63285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2325 q ha hb
    | true =>
      simp only [d50, d63285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d51 q = 1) (hb : d63286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d63286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51, d63286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d4341 q = 1) (hb : d63316 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d63316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4341, d63316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51644 q = 1) (hb : d63317 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d63317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51644, d63317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51645 q = 1) (hb : d63318 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d63318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51645, d63318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d63318 q = 1) (hb : d63631 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d63631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro2333 (p : Pattern) (ha : d63325 p = 1) (hb : d63637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d407 q = 1) (hb : d63304 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d63304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d63304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2328 q ha hb
  have h2 (q : Pattern) (ha : d53639 q = 1) (hb : d63305 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d63305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53639, d63305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63306 q = 1) (hb : d63630 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63306, d63630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63306, d63630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d63319 q = 1) (hb : d63632 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63319, d63632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63319, d63632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2332 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d63320 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d63321 q = 1) (hb : d63633 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63321, d63633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63321, d63633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d63322 q = 1) (hb : d63634 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63322, d63634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63322, d63634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d63323 q = 1) (hb : d63635 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63323, d63635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63323, d63635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d63324 q = 1) (hb : d63636 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63324, d63636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d63324, d63636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d63325 q = 1) (hb : d63637 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63325, d63637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d63325, d63637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro2334 (p : Pattern) (ha : d53655 p = 1) (hb : d63334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d63314 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d63314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2331 q ha hb
    | true =>
      simp only [d204, d63314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2325 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d63331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d63331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287, d63331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d63332 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d63332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d63332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d63333 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d63333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289, d63333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d63334 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d63334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290, d63334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d63334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2335 (p : Pattern) (ha : d376 p = 1) (hb : d52094 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d295 q = 1) (hb : d52094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52094 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d376 q = 1) (hb : d52094 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2336 (p : Pattern) (ha : d381 p = 1) (hb : d52101 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d301 q = 1) (hb : d52100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302 q = 1) (hb : d52101 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d302, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52101 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d381 q = 1) (hb : d52101 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2337 (p : Pattern) (ha : d385 p = 1) (hb : d52134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331 q = 1) (hb : d52130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44 q ha hb
    | true =>
      simp only [d331, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d332 q = 1) (hb : d52131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d332, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21 q ha hb
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d333 q = 1) (hb : d52132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d334 q = 1) (hb : d52133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d334, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d335 q = 1) (hb : d52134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d335, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52134 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d385 q = 1) (hb : d52134 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2338 (p : Pattern) (ha : d63351 p = 1) (hb : d63644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63351 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d377 q = 1) (hb : d63338 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d63338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2335 q ha hb
    | true =>
      simp only [d377, d63338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2329 q ha hb
  have h3 (q : Pattern) (ha : d378 q = 1) (hb : d63339 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d63339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d378, d63339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379 q = 1) (hb : d63340 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d63340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379, d63340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d380 q = 1) (hb : d63341 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d63341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380, d63341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d382 q = 1) (hb : d63342 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d63342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2336 q ha hb
    | true =>
      simp only [d382, d63342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2330 q ha hb
  have h7 (q : Pattern) (ha : d383 q = 1) (hb : d63343 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d63343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d383, d63343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d384 q = 1) (hb : d63344 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d63344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d384, d63344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d386 q = 1) (hb : d63345 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d63345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2337 q ha hb
    | true =>
      simp only [d386, d63345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2331 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d63314 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4376 q = 1) (hb : d63346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d63346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4376, d63346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d390 q = 1) (hb : d63347 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d63347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2331 q ha hb
    | true =>
      simp only [d390, d63347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d391 q = 1) (hb : d63348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d63348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d391, d63348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d4377 q = 1) (hb : d63349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d63349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4377, d63349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51661 q = 1) (hb : d63350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51661, d63350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51661, d63350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51662 q = 1) (hb : d63351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51662, d63351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51662, d63351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d63351 q = 1) (hb : d63644 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d63644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro2339 (p : Pattern) (ha : d63358 p = 1) (hb : d63650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53656 q = 1) (hb : d63335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d63335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d63335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2334 q ha hb
  have h2 (q : Pattern) (ha : d53657 q = 1) (hb : d63336 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d63336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53657, d63336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63337 q = 1) (hb : d63643 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63337, d63643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63337, d63643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d63352 q = 1) (hb : d63645 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63352, d63645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63352, d63645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2338 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d63334 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d407 q = 1) (hb : d63353 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d63353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d407, d63353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2328 q ha hb
  have h7 (q : Pattern) (ha : d63354 q = 1) (hb : d63646 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63354, d63646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63354, d63646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d63355 q = 1) (hb : d63647 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63355, d63647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63355, d63647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d63356 q = 1) (hb : d63648 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63356, d63648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63356, d63648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d63357 q = 1) (hb : d63649 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63357, d63649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d63357, d63649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d63358 q = 1) (hb : d63650 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63358, d63650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d63358, d63650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro2340 (p : Pattern) (ha : d63364 p = 1) (hb : d63656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63296 q = 1) (hb : d63626 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63296, d63626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63296, d63626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2327 q ha hb
  have h2 (q : Pattern) (ha : d63297 q = 1) (hb : d63627 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63297, d63627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63297, d63627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63298 q = 1) (hb : d63628 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63298, d63628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63298, d63628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63299 q = 1) (hb : d63629 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63299, d63629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63299, d63629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63326 q = 1) (hb : d63638 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63326, d63638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63326, d63638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2333 q ha hb
  have h6 (q : Pattern) (ha : d63327 q = 1) (hb : d63639 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63327, d63639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63327, d63639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63328 q = 1) (hb : d63640 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63328, d63640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63328, d63640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d63329 q = 1) (hb : d63641 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63329, d63641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63329, d63641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d63330 q = 1) (hb : d63642 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63330, d63642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63330, d63642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d63359 q = 1) (hb : d63651 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63359, d63651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63359, d63651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2339 q ha hb
  have h11 (q : Pattern) (ha : d63360 q = 1) (hb : d63652 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63360, d63652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63360, d63652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d63361 q = 1) (hb : d63653 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63361, d63653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63361, d63653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d63362 q = 1) (hb : d63654 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63362, d63654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63362, d63654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d63363 q = 1) (hb : d63655 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63363, d63655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63363, d63655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d63364 q = 1) (hb : d63656 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63364, d63656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d63364, d63656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro2341 (p : Pattern) (ha : d501 p = 1) (hb : d52237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d52236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d52237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d52237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d52237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52237 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d501 q = 1) (hb : d52237 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2342 (p : Pattern) (ha : d653 p = 1) (hb : d63392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63392 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d639 q = 1) (hb : d63388 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d63388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2341 q ha hb
    | true =>
      simp only [d639, d63388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d640 q = 1) (hb : d63389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d63389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d640, d63389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d641 q = 1) (hb : d63390 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d63390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d641, d63390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d642 q = 1) (hb : d63391 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d63391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d642, d63391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d643 q = 1) (hb : d63392 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d63392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d643, d63392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d653 q = 1) (hb : d63392 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2343 (p : Pattern) (ha : d500 p = 1) (hb : d52233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60 q ha hb
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d485 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d485, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d486 q = 1) (hb : d52233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d486, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d486, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52233 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d500 q = 1) (hb : d52233 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2344 (p : Pattern) (ha : d53680 p = 1) (hb : d63369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63369 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d502 q = 1) (hb : d63365 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d63365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2343 q ha hb
    | true =>
      simp only [d502, d63365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2341 q ha hb
  have h3 (q : Pattern) (ha : d503 q = 1) (hb : d63366 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d63366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d503, d63366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d504 q = 1) (hb : d63367 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d63367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d504, d63367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d505 q = 1) (hb : d63368 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d63368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d505, d63368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d506 q = 1) (hb : d63369 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d63369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d506, d63369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53680 q = 1) (hb : d63369 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2345 (p : Pattern) (ha : d609 p = 1) (hb : d52258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60 q ha hb
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d485 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d485, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d511 q = 1) (hb : d52258 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d52258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d511, d52258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52258 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d609 q = 1) (hb : d52258 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2346 (p : Pattern) (ha : d610 p = 1) (hb : d52260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d52236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d52260 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d52260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d52260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52260 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d610 q = 1) (hb : d52260 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2347 (p : Pattern) (ha : d615 p = 1) (hb : d52267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60 q ha hb
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d519 q = 1) (hb : d52266 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d52266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d519, d52266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d520 q = 1) (hb : d52267 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d52267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d520, d52267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52267 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d615 q = 1) (hb : d52267 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2348 (p : Pattern) (ha : d616 p = 1) (hb : d52270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d52269 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d52269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d52269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d52270 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d52270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d52270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52270 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d616 q = 1) (hb : d52270 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2349 (p : Pattern) (ha : d620 p = 1) (hb : d52306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d555 q = 1) (hb : d52302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78 q ha hb
    | true =>
      simp only [d555, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d556 q = 1) (hb : d52303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d556, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d478 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60 q ha hb
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d479 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d557 q = 1) (hb : d52304 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, d52304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d557, d52304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d558 q = 1) (hb : d52305 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, d52305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d558, d52305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d559 q = 1) (hb : d52306 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, d52306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d559, d52306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52306 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d620 q = 1) (hb : d52306 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2350 (p : Pattern) (ha : d63386 p = 1) (hb : d63658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63386 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d611 q = 1) (hb : d63373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d611, d63373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2345 q ha hb
    | true =>
      simp only [d611, d63373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2346 q ha hb
  have h3 (q : Pattern) (ha : d612 q = 1) (hb : d63374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, d63374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d612, d63374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d613 q = 1) (hb : d63375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d63375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d613, d63375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d614 q = 1) (hb : d63376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, d63376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d614, d63376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d617 q = 1) (hb : d63377 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, d63377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2347 q ha hb
    | true =>
      simp only [d617, d63377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2348 q ha hb
  have h7 (q : Pattern) (ha : d618 q = 1) (hb : d63378 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d63378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d618, d63378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d619 q = 1) (hb : d63379 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d63379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d619, d63379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d621 q = 1) (hb : d63380 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d63380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2349 q ha hb
    | true =>
      simp only [d621, d63380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2343 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d63365 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4413 q = 1) (hb : d63381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d63381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4413, d63381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d626 q = 1) (hb : d63382 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d63382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2343 q ha hb
    | true =>
      simp only [d626, d63382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d627 q = 1) (hb : d63383 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d63383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d627, d63383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d4414 q = 1) (hb : d63384 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d63384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4414, d63384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51686 q = 1) (hb : d63385 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51686, d63385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51686, d63385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51687 q = 1) (hb : d63386 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51687, d63386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51687, d63386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d63386 q = 1) (hb : d63658 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d63658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro2351 (p : Pattern) (ha : d63398 p = 1) (hb : d63664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53681 q = 1) (hb : d63370 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d63370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, d63370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2344 q ha hb
  have h2 (q : Pattern) (ha : d53682 q = 1) (hb : d63371 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d63371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53682, d63371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63372 q = 1) (hb : d63657 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63372, d63657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63372, d63657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d63387 q = 1) (hb : d63659 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63387, d63659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63387, d63659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2350 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d63369 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d654 q = 1) (hb : d63393 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d63393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d654, d63393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2342 q ha hb
  have h7 (q : Pattern) (ha : d63394 q = 1) (hb : d63660 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63394, d63660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63394, d63660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d63395 q = 1) (hb : d63661 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63395, d63661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63395, d63661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d63396 q = 1) (hb : d63662 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63396, d63662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63396, d63662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d63397 q = 1) (hb : d63663 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63397, d63663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d63397, d63663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d63398 q = 1) (hb : d63664 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63398, d63664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d63398, d63664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro2352 (p : Pattern) (ha : d63404 p = 1) (hb : d63670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63399 q = 1) (hb : d63665 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63399, d63665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63399, d63665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2351 q ha hb
  have h2 (q : Pattern) (ha : d63400 q = 1) (hb : d63666 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63400, d63666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63400, d63666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63401 q = 1) (hb : d63667 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63401, d63667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63401, d63667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63402 q = 1) (hb : d63668 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63402, d63668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63402, d63668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63403 q = 1) (hb : d63669 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63403, d63669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63403, d63669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63404 q = 1) (hb : d63670 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63404, d63670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63404, d63670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2353 (p : Pattern) (ha : d793 p = 1) (hb : d52459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d52457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d52458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d52459 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d52459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d52459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52459 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d793 q = 1) (hb : d52459 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2354 (p : Pattern) (ha : d959 p = 1) (hb : d63433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63433 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d945 q = 1) (hb : d63429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d63429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2353 q ha hb
    | true =>
      simp only [d945, d63429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d946 q = 1) (hb : d63430 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d63430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d946, d63430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d947 q = 1) (hb : d63431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d63431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d947, d63431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d948 q = 1) (hb : d63432 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d63432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d948, d63432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d949 q = 1) (hb : d63433 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d63433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d949, d63433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d959 q = 1) (hb : d63433 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2355 (p : Pattern) (ha : d792 p = 1) (hb : d52455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104 q ha hb
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d52454 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d778 q = 1) (hb : d52455 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, d52455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d778, d52455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52455 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d792 q = 1) (hb : d52455 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2356 (p : Pattern) (ha : d53707 p = 1) (hb : d63410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63410 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d794 q = 1) (hb : d63406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d63406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2355 q ha hb
    | true =>
      simp only [d794, d63406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2353 q ha hb
  have h3 (q : Pattern) (ha : d795 q = 1) (hb : d63407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d63407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d795, d63407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d796 q = 1) (hb : d63408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d63408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d796, d63408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d797 q = 1) (hb : d63409 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d63409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d797, d63409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d798 q = 1) (hb : d63410 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d63410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d798, d63410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53707 q = 1) (hb : d63410 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2357 (p : Pattern) (ha : d915 p = 1) (hb : d52480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104 q ha hb
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d52454 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d803 q = 1) (hb : d52480 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d52480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d52480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52480 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d915 q = 1) (hb : d52480 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2358 (p : Pattern) (ha : d916 p = 1) (hb : d52482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d52457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d52458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d52482 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d52482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d52482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52482 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d916 q = 1) (hb : d52482 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2359 (p : Pattern) (ha : d921 p = 1) (hb : d52489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104 q ha hb
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d811 q = 1) (hb : d52488 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d52488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d52488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d812 q = 1) (hb : d52489 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d52489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d812, d52489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52489 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d921 q = 1) (hb : d52489 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2360 (p : Pattern) (ha : d922 p = 1) (hb : d52492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d52457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d52491 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d52491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d52491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d52492 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d52492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d52492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52492 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d922 q = 1) (hb : d52492 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2361 (p : Pattern) (ha : d926 p = 1) (hb : d52527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d52523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro124 q ha hb
    | true =>
      simp only [d846, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d52524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d770 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104 q ha hb
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d771 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d848 q = 1) (hb : d52525 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, d52525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d848, d52525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d849 q = 1) (hb : d52526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, d52526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d849, d52526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d850 q = 1) (hb : d52527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, d52527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d850, d52527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52527 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d926 q = 1) (hb : d52527 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2362 (p : Pattern) (ha : d63427 p = 1) (hb : d63673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63427 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d917 q = 1) (hb : d63414 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, d63414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2357 q ha hb
    | true =>
      simp only [d917, d63414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2358 q ha hb
  have h3 (q : Pattern) (ha : d918 q = 1) (hb : d63415 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d63415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d918, d63415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d919 q = 1) (hb : d63416 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d63416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d919, d63416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d920 q = 1) (hb : d63417 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, d63417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d920, d63417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d923 q = 1) (hb : d63418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, d63418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2359 q ha hb
    | true =>
      simp only [d923, d63418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2360 q ha hb
  have h7 (q : Pattern) (ha : d924 q = 1) (hb : d63419 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d63419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d924, d63419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d925 q = 1) (hb : d63420 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d63420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d925, d63420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d927 q = 1) (hb : d63421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d63421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2361 q ha hb
    | true =>
      simp only [d927, d63421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2355 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d63406 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4451 q = 1) (hb : d63422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d63422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4451, d63422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d932 q = 1) (hb : d63423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d63423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2355 q ha hb
    | true =>
      simp only [d932, d63423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d933 q = 1) (hb : d63424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d63424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d933, d63424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d4452 q = 1) (hb : d63425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d63425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4452, d63425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51712 q = 1) (hb : d63426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51712, d63426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51712, d63426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51713 q = 1) (hb : d63427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51713, d63427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51713, d63427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d63427 q = 1) (hb : d63673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d63673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro2363 (p : Pattern) (ha : d63439 p = 1) (hb : d63679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53708 q = 1) (hb : d63411 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d63411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, d63411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2356 q ha hb
  have h2 (q : Pattern) (ha : d53709 q = 1) (hb : d63412 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d63412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53709, d63412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63413 q = 1) (hb : d63672 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63413, d63672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63413, d63672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d63428 q = 1) (hb : d63674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63428, d63674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63428, d63674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2362 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d63410 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d960 q = 1) (hb : d63434 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d63434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d960, d63434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2354 q ha hb
  have h7 (q : Pattern) (ha : d63435 q = 1) (hb : d63675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63435, d63675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63435, d63675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d63436 q = 1) (hb : d63676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63436, d63676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63436, d63676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d63437 q = 1) (hb : d63677 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63437, d63677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63437, d63677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d63438 q = 1) (hb : d63678 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63438, d63678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d63438, d63678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d63439 q = 1) (hb : d63679 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63439, d63679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d63439, d63679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro2364 (p : Pattern) (ha : d63445 p = 1) (hb : d63685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63440 q = 1) (hb : d63680 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63440, d63680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63440, d63680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2363 q ha hb
  have h2 (q : Pattern) (ha : d63441 q = 1) (hb : d63681 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63441, d63681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63441, d63681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63442 q = 1) (hb : d63682 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63442, d63682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63442, d63682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63443 q = 1) (hb : d63683 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63443, d63683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63443, d63683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63444 q = 1) (hb : d63684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63444, d63684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63444, d63684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63445 q = 1) (hb : d63685 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63445, d63685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63445, d63685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2365 (p : Pattern) (ha : d1172 p = 1) (hb : d52742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d52740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d52741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d52741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d52741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d52742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d52742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d52742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52742 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1172 q = 1) (hb : d52742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2366 (p : Pattern) (ha : d1370 p = 1) (hb : d63475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63475 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1356 q = 1) (hb : d63471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d63471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2365 q ha hb
    | true =>
      simp only [d1356, d63471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1357 q = 1) (hb : d63472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d63472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1357, d63472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1358 q = 1) (hb : d63473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d63473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1358, d63473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1359 q = 1) (hb : d63474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d63474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1359, d63474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1360 q = 1) (hb : d63475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d63475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1360, d63475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1370 q = 1) (hb : d63475 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2367 (p : Pattern) (ha : d1171 p = 1) (hb : d52738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro156 q ha hb
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1157 q = 1) (hb : d52738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1157, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52738 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1171 q = 1) (hb : d52738 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2368 (p : Pattern) (ha : d53735 p = 1) (hb : d63452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63452 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1173 q = 1) (hb : d63448 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d63448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2367 q ha hb
    | true =>
      simp only [d1173, d63448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2365 q ha hb
  have h3 (q : Pattern) (ha : d1174 q = 1) (hb : d63449 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d63449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1174, d63449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1175 q = 1) (hb : d63450 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d63450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1175, d63450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1176 q = 1) (hb : d63451 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d63451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1176, d63451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1177 q = 1) (hb : d63452 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d63452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1177, d63452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53735 q = 1) (hb : d63452 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2369 (p : Pattern) (ha : d1326 p = 1) (hb : d52763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro156 q ha hb
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1182 q = 1) (hb : d52763 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52763 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1326 q = 1) (hb : d52763 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2370 (p : Pattern) (ha : d1327 p = 1) (hb : d52765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d52740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d52741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d52741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d52741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d52765 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d52765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d52765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52765 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1327 q = 1) (hb : d52765 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2371 (p : Pattern) (ha : d1332 p = 1) (hb : d52772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro156 q ha hb
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1190 q = 1) (hb : d52771 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1191 q = 1) (hb : d52772 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1191, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52772 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1332 q = 1) (hb : d52772 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2372 (p : Pattern) (ha : d1333 p = 1) (hb : d52775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d52740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d52774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d52774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d52774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d52775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d52775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d52775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52775 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1333 q = 1) (hb : d52775 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2373 (p : Pattern) (ha : d1337 p = 1) (hb : d52807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d52803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro176 q ha hb
    | true =>
      simp only [d1222, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d52804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1149 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro156 q ha hb
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1150 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1224 q = 1) (hb : d52805 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, d52805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1224, d52805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1225 q = 1) (hb : d52806 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, d52806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1225, d52806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1226 q = 1) (hb : d52807 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, d52807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1226, d52807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52807 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1337 q = 1) (hb : d52807 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2374 (p : Pattern) (ha : d63469 p = 1) (hb : d63689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63469 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1328 q = 1) (hb : d63456 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d63456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2369 q ha hb
    | true =>
      simp only [d1328, d63456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2370 q ha hb
  have h3 (q : Pattern) (ha : d1329 q = 1) (hb : d63457 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d63457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1329, d63457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1330 q = 1) (hb : d63458 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d63458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1330, d63458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1331 q = 1) (hb : d63459 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d63459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1331, d63459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1334 q = 1) (hb : d63460 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d63460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2371 q ha hb
    | true =>
      simp only [d1334, d63460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2372 q ha hb
  have h7 (q : Pattern) (ha : d1335 q = 1) (hb : d63461 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d63461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1335, d63461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1336 q = 1) (hb : d63462 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d63462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1336, d63462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1338 q = 1) (hb : d63463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d63463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2373 q ha hb
    | true =>
      simp only [d1338, d63463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2367 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d63448 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4490 q = 1) (hb : d63464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d63464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4490, d63464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1343 q = 1) (hb : d63465 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d63465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2367 q ha hb
    | true =>
      simp only [d1343, d63465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1344 q = 1) (hb : d63466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d63466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1344, d63466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d4491 q = 1) (hb : d63467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d63467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4491, d63467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51739 q = 1) (hb : d63468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51739, d63468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51739, d63468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51740 q = 1) (hb : d63469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51740, d63469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51740, d63469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d63469 q = 1) (hb : d63689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d63689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro2375 (p : Pattern) (ha : d63481 p = 1) (hb : d63695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53736 q = 1) (hb : d63453 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d63453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, d63453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2368 q ha hb
  have h2 (q : Pattern) (ha : d53737 q = 1) (hb : d63454 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d63454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53737, d63454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63455 q = 1) (hb : d63688 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63455, d63688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63455, d63688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d63470 q = 1) (hb : d63690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63470, d63690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63470, d63690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2374 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d63452 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1371 q = 1) (hb : d63476 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d63476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1371, d63476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2366 q ha hb
  have h7 (q : Pattern) (ha : d63477 q = 1) (hb : d63691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63477, d63691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63477, d63691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d63478 q = 1) (hb : d63692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63478, d63692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63478, d63692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d63479 q = 1) (hb : d63693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63479, d63693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63479, d63693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d63480 q = 1) (hb : d63694 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63480, d63694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d63480, d63694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d63481 q = 1) (hb : d63695 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63481, d63695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d63481, d63695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro2376 (p : Pattern) (ha : d63487 p = 1) (hb : d63701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63482 q = 1) (hb : d63696 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63482, d63696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63482, d63696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2375 q ha hb
  have h2 (q : Pattern) (ha : d63483 q = 1) (hb : d63697 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63483, d63697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63483, d63697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63484 q = 1) (hb : d63698 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63484, d63698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63484, d63698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63485 q = 1) (hb : d63699 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63485, d63699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63485, d63699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63486 q = 1) (hb : d63700 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63486, d63700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63486, d63700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63487 q = 1) (hb : d63701 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63487, d63701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63487, d63701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2377 (p : Pattern) (ha : d1633 p = 1) (hb : d53063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d53061 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d53062 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d53062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d53062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d53063 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d53063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d53063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53063 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1633 q = 1) (hb : d53063 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2378 (p : Pattern) (ha : d1847 p = 1) (hb : d63518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1833 q = 1) (hb : d63514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d63514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2377 q ha hb
    | true =>
      simp only [d1833, d63514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1834 q = 1) (hb : d63515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d63515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1834, d63515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1835 q = 1) (hb : d63516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d63516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1835, d63516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1836 q = 1) (hb : d63517 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d63517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1836, d63517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1837 q = 1) (hb : d63518 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d63518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1837, d63518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1847 q = 1) (hb : d63518 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2379 (p : Pattern) (ha : d1632 p = 1) (hb : d53059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro214 q ha hb
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1618 q = 1) (hb : d53059 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1618, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53059 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1632 q = 1) (hb : d53059 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2380 (p : Pattern) (ha : d53764 p = 1) (hb : d63495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1634 q = 1) (hb : d63491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d63491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2379 q ha hb
    | true =>
      simp only [d1634, d63491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2377 q ha hb
  have h3 (q : Pattern) (ha : d1635 q = 1) (hb : d63492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d63492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1635, d63492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1636 q = 1) (hb : d63493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d63493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1636, d63493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1637 q = 1) (hb : d63494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d63494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1637, d63494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1638 q = 1) (hb : d63495 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d63495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1638, d63495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53764 q = 1) (hb : d63495 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2381 (p : Pattern) (ha : d1803 p = 1) (hb : d53084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro214 q ha hb
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1643 q = 1) (hb : d53084 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53084 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1803 q = 1) (hb : d53084 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2382 (p : Pattern) (ha : d1804 p = 1) (hb : d53086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d53061 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d53062 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d53062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d53062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d53086 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d53086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d53086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53086 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1804 q = 1) (hb : d53086 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2383 (p : Pattern) (ha : d1809 p = 1) (hb : d53093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro214 q ha hb
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1651 q = 1) (hb : d53092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1652 q = 1) (hb : d53093 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1652, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53093 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1809 q = 1) (hb : d53093 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2384 (p : Pattern) (ha : d1810 p = 1) (hb : d53096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d53061 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d53095 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d53095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d53095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d53096 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d53096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d53096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53096 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1810 q = 1) (hb : d53096 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2385 (p : Pattern) (ha : d1814 p = 1) (hb : d53122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d53118 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro232 q ha hb
    | true =>
      simp only [d1677, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d53119 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1610 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro214 q ha hb
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1611 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1679 q = 1) (hb : d53120 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, d53120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1679, d53120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1680 q = 1) (hb : d53121 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, d53121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1680, d53121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1681 q = 1) (hb : d53122 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, d53122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1681, d53122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53122 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1814 q = 1) (hb : d53122 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2386 (p : Pattern) (ha : d63512 p = 1) (hb : d63706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63512 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1805 q = 1) (hb : d63499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d63499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2381 q ha hb
    | true =>
      simp only [d1805, d63499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2382 q ha hb
  have h3 (q : Pattern) (ha : d1806 q = 1) (hb : d63500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d63500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1806, d63500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1807 q = 1) (hb : d63501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d63501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1807, d63501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1808 q = 1) (hb : d63502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d63502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1808, d63502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1811 q = 1) (hb : d63503 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d63503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2383 q ha hb
    | true =>
      simp only [d1811, d63503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2384 q ha hb
  have h7 (q : Pattern) (ha : d1812 q = 1) (hb : d63504 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d63504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1812, d63504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1813 q = 1) (hb : d63505 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d63505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1813, d63505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1815 q = 1) (hb : d63506 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d63506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2385 q ha hb
    | true =>
      simp only [d1815, d63506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2379 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d63491 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4530 q = 1) (hb : d63507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d63507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4530, d63507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1820 q = 1) (hb : d63508 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d63508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2379 q ha hb
    | true =>
      simp only [d1820, d63508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1821 q = 1) (hb : d63509 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d63509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1821, d63509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d4531 q = 1) (hb : d63510 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d63510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4531, d63510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51767 q = 1) (hb : d63511 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51767, d63511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51767, d63511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51768 q = 1) (hb : d63512 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51768, d63512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51768, d63512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d63512 q = 1) (hb : d63706 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d63706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro2387 (p : Pattern) (ha : d63524 p = 1) (hb : d63712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53765 q = 1) (hb : d63496 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d63496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, d63496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2380 q ha hb
  have h2 (q : Pattern) (ha : d53766 q = 1) (hb : d63497 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d63497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53766, d63497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63498 q = 1) (hb : d63705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63498, d63705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63498, d63705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d63513 q = 1) (hb : d63707 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63513, d63707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63513, d63707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2386 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d63495 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1848 q = 1) (hb : d63519 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d63519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1848, d63519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2378 q ha hb
  have h7 (q : Pattern) (ha : d63520 q = 1) (hb : d63708 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63520, d63708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63520, d63708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d63521 q = 1) (hb : d63709 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63521, d63709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63521, d63709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d63522 q = 1) (hb : d63710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63522, d63710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63522, d63710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d63523 q = 1) (hb : d63711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63523, d63711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d63523, d63711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d63524 q = 1) (hb : d63712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63524, d63712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d63524, d63712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro2388 (p : Pattern) (ha : d63530 p = 1) (hb : d63718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63525 q = 1) (hb : d63713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63525, d63713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63525, d63713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2387 q ha hb
  have h2 (q : Pattern) (ha : d63526 q = 1) (hb : d63714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63526, d63714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63526, d63714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63527 q = 1) (hb : d63715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63527, d63715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63527, d63715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63528 q = 1) (hb : d63716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63528, d63716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63528, d63716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63529 q = 1) (hb : d63717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63529, d63717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63529, d63717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63530 q = 1) (hb : d63718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63530, d63718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63530, d63718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2389 (p : Pattern) (ha : d2116 p = 1) (hb : d53384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d53382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d53383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d53383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d53383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d53384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d53384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d53384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53384 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2116 q = 1) (hb : d53384 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2390 (p : Pattern) (ha : d2325 p = 1) (hb : d63562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63562 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2311 q = 1) (hb : d63558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d63558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2389 q ha hb
    | true =>
      simp only [d2311, d63558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2312 q = 1) (hb : d63559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d63559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2312, d63559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2313 q = 1) (hb : d63560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d63560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2313, d63560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2314 q = 1) (hb : d63561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d63561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2314, d63561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2315 q = 1) (hb : d63562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d63562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2315, d63562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2325 q = 1) (hb : d63562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2391 (p : Pattern) (ha : d2115 p = 1) (hb : d53380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro273 q ha hb
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2101 q = 1) (hb : d53380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2101, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53380 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2115 q = 1) (hb : d53380 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2392 (p : Pattern) (ha : d53794 p = 1) (hb : d63539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63539 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2117 q = 1) (hb : d63535 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d63535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2391 q ha hb
    | true =>
      simp only [d2117, d63535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2389 q ha hb
  have h3 (q : Pattern) (ha : d2118 q = 1) (hb : d63536 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d63536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2118, d63536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2119 q = 1) (hb : d63537 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d63537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2119, d63537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2120 q = 1) (hb : d63538 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d63538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2120, d63538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2121 q = 1) (hb : d63539 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d63539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2121, d63539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53794 q = 1) (hb : d63539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2393 (p : Pattern) (ha : d2281 p = 1) (hb : d53405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro273 q ha hb
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2126 q = 1) (hb : d53405 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2126, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53405 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2281 q = 1) (hb : d53405 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2394 (p : Pattern) (ha : d2282 p = 1) (hb : d53407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d53382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d53383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d53383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d53383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d53407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d53407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d53407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53407 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2282 q = 1) (hb : d53407 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2395 (p : Pattern) (ha : d2287 p = 1) (hb : d53414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro273 q ha hb
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2134 q = 1) (hb : d53413 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2134, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2135 q = 1) (hb : d53414 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2135, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53414 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2287 q = 1) (hb : d53414 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2396 (p : Pattern) (ha : d2288 p = 1) (hb : d53417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d53382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d53416 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d53416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d53416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d53417 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d53417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d53417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53417 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2288 q = 1) (hb : d53417 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro2397 (p : Pattern) (ha : d2292 p = 1) (hb : d53439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d53435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro291 q ha hb
    | true =>
      simp only [d2156, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d53436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2093 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro273 q ha hb
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2094 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2158 q = 1) (hb : d53437 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2158, d53437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2158, d53437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2159 q = 1) (hb : d53438 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2159, d53438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2159, d53438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2160 q = 1) (hb : d53439 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2160, d53439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2160, d53439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53439 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2292 q = 1) (hb : d53439 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro2398 (p : Pattern) (ha : d63556 p = 1) (hb : d63724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63556 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2283 q = 1) (hb : d63543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, d63543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2393 q ha hb
    | true =>
      simp only [d2283, d63543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2394 q ha hb
  have h3 (q : Pattern) (ha : d2284 q = 1) (hb : d63544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d63544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2284, d63544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2285 q = 1) (hb : d63545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d63545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2285, d63545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2286 q = 1) (hb : d63546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d63546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2286, d63546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2289 q = 1) (hb : d63547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d63547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2395 q ha hb
    | true =>
      simp only [d2289, d63547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2396 q ha hb
  have h7 (q : Pattern) (ha : d2290 q = 1) (hb : d63548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d63548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2290, d63548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2291 q = 1) (hb : d63549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d63549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2291, d63549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2293 q = 1) (hb : d63550 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d63550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2397 q ha hb
    | true =>
      simp only [d2293, d63550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2391 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d63535 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4571 q = 1) (hb : d63551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d63551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4571, d63551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2298 q = 1) (hb : d63552 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d63552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2391 q ha hb
    | true =>
      simp only [d2298, d63552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d2299 q = 1) (hb : d63553 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d63553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2299, d63553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d4572 q = 1) (hb : d63554 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d63554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4572, d63554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51796 q = 1) (hb : d63555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51796, d63555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51796, d63555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51797 q = 1) (hb : d63556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51797, d63556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51797, d63556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d63556 q = 1) (hb : d63724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d63724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro2399 (p : Pattern) (ha : d63568 p = 1) (hb : d63730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53795 q = 1) (hb : d63540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d63540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, d63540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2392 q ha hb
  have h2 (q : Pattern) (ha : d53796 q = 1) (hb : d63541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d63541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53796, d63541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63542 q = 1) (hb : d63723 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63542, d63723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63542, d63723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d63557 q = 1) (hb : d63725 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63557, d63725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63557, d63725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2398 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d63539 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2326 q = 1) (hb : d63563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d63563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2326, d63563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2390 q ha hb
  have h7 (q : Pattern) (ha : d63564 q = 1) (hb : d63726 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63564, d63726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63564, d63726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d63565 q = 1) (hb : d63727 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63565, d63727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63565, d63727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d63566 q = 1) (hb : d63728 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63566, d63728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63566, d63728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d63567 q = 1) (hb : d63729 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63567, d63729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d63567, d63729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d63568 q = 1) (hb : d63730 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63568, d63730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d63568, d63730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro2400 (p : Pattern) (ha : d63574 p = 1) (hb : d63736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63569 q = 1) (hb : d63731 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63569, d63731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63569, d63731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2399 q ha hb
  have h2 (q : Pattern) (ha : d63570 q = 1) (hb : d63732 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63570, d63732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63570, d63732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63571 q = 1) (hb : d63733 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63571, d63733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63571, d63733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63572 q = 1) (hb : d63734 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63572, d63734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63572, d63734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63573 q = 1) (hb : d63735 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63573, d63735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63573, d63735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63574 q = 1) (hb : d63736 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63574, d63736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63574, d63736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2401 (p : Pattern) (ha : d63580 p = 1) (hb : d63742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d63405 q = 1) (hb : d63671 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63405, d63671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2340 q ha hb
    | true =>
      simp only [d63405, d63671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2352 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d63446 q = 1) (hb : d63686 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63446, d63686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63446, d63686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2364 q ha hb
  have h3 (q : Pattern) (ha : d63447 q = 1) (hb : d63687 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63447, d63687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63447, d63687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63488 q = 1) (hb : d63702 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63488, d63702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63488, d63702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2376 q ha hb
  have h5 (q : Pattern) (ha : d63489 q = 1) (hb : d63703 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63489, d63703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63489, d63703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63490 q = 1) (hb : d63704 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d63490, d63704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63490, d63704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63531 q = 1) (hb : d63719 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63531, d63719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63531, d63719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2388 q ha hb
  have h8 (q : Pattern) (ha : d63532 q = 1) (hb : d63720 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63532, d63720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63532, d63720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d63533 q = 1) (hb : d63721 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d63533, d63721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63533, d63721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d63534 q = 1) (hb : d63722 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d63534, d63722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63534, d63722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d63575 q = 1) (hb : d63737 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63575, d63737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63575, d63737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2400 q ha hb
  have h12 (q : Pattern) (ha : d63576 q = 1) (hb : d63738 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63576, d63738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63576, d63738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d63577 q = 1) (hb : d63739 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d63577, d63739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63577, d63739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d63578 q = 1) (hb : d63740 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d63578, d63740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63578, d63740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d63579 q = 1) (hb : d63741 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d63579, d63741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d63579, d63741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d63580 q = 1) (hb : d63742 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d63580, d63742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d63580, d63742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro2402 (p : Pattern) (ha : d63586 p = 1) (hb : d63748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63581 q = 1) (hb : d63743 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d63581, d63743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2401 q ha hb
    | true =>
      simp only [d63581, d63743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63582 q = 1) (hb : d63744 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d63582, d63744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63582, d63744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63583 q = 1) (hb : d63745 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d63583, d63745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63583, d63745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63584 q = 1) (hb : d63746 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d63584, d63746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63584, d63746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63585 q = 1) (hb : d63747 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d63585, d63747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63585, d63747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63586 q = 1) (hb : d63748 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d63586, d63748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63586, d63748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2403 (p : Pattern) (ha : d63592 p = 1) (hb : d63754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63587 q = 1) (hb : d63749 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d63587, d63749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2402 q ha hb
    | true =>
      simp only [d63587, d63749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63588 q = 1) (hb : d63750 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d63588, d63750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63588, d63750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63589 q = 1) (hb : d63751 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d63589, d63751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63589, d63751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63590 q = 1) (hb : d63752 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d63590, d63752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63590, d63752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63591 q = 1) (hb : d63753 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d63591, d63753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63591, d63753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63592 q = 1) (hb : d63754 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d63592, d63754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63592, d63754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2404 (p : Pattern) (ha : d63598 p = 1) (hb : d63760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63593 q = 1) (hb : d63755 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d63593, d63755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2403 q ha hb
    | true =>
      simp only [d63593, d63755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63594 q = 1) (hb : d63756 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d63594, d63756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63594, d63756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63595 q = 1) (hb : d63757 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d63595, d63757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63595, d63757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63596 q = 1) (hb : d63758 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d63596, d63758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63596, d63758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63597 q = 1) (hb : d63759 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d63597, d63759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63597, d63759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63598 q = 1) (hb : d63760 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d63598, d63760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63598, d63760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2405 (p : Pattern) (ha : d63604 p = 1) (hb : d63766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63599 q = 1) (hb : d63761 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d63599, d63761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2404 q ha hb
    | true =>
      simp only [d63599, d63761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63600 q = 1) (hb : d63762 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d63600, d63762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63600, d63762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63601 q = 1) (hb : d63763 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d63601, d63763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63601, d63763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63602 q = 1) (hb : d63764 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d63602, d63764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63602, d63764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63603 q = 1) (hb : d63765 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d63603, d63765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63603, d63765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63604 q = 1) (hb : d63766 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d63604, d63766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63604, d63766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2406 (p : Pattern) (ha : d63610 p = 1) (hb : d63772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63605 q = 1) (hb : d63767 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d63605, d63767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2405 q ha hb
    | true =>
      simp only [d63605, d63767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63606 q = 1) (hb : d63768 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d63606, d63768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63606, d63768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63607 q = 1) (hb : d63769 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d63607, d63769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63607, d63769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63608 q = 1) (hb : d63770 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d63608, d63770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63608, d63770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63609 q = 1) (hb : d63771 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d63609, d63771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63609, d63771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63610 q = 1) (hb : d63772 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d63610, d63772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63610, d63772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2407 (p : Pattern) (ha : d63616 p = 1) (hb : d63778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63611 q = 1) (hb : d63773 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d63611, d63773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2406 q ha hb
    | true =>
      simp only [d63611, d63773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63612 q = 1) (hb : d63774 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d63612, d63774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63612, d63774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63613 q = 1) (hb : d63775 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d63613, d63775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63613, d63775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63614 q = 1) (hb : d63776 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d63614, d63776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63614, d63776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63615 q = 1) (hb : d63777 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d63615, d63777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63615, d63777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63616 q = 1) (hb : d63778 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d63616, d63778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63616, d63778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2408 (p : Pattern) (ha : d63622 p = 1) (hb : d63784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63617 q = 1) (hb : d63779 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d63617, d63779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2407 q ha hb
    | true =>
      simp only [d63617, d63779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63618 q = 1) (hb : d63780 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d63618, d63780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63618, d63780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63619 q = 1) (hb : d63781 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d63619, d63781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63619, d63781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63620 q = 1) (hb : d63782 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d63620, d63782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63620, d63782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63621 q = 1) (hb : d63783 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d63621, d63783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63621, d63783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63622 q = 1) (hb : d63784 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d63622, d63784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63622, d63784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2409 (p : Pattern) (ha : d54865 p = 1) (hb : d62939 p = 1) : d63787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d62938 q = 1) : d407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2223 q ha hb
    | true =>
      simp only [d112, d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2224 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d62938 q = 1) : d53639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d62938 q = 1) : d53640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d62938 q = 1) : d63785 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d63785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d63785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54864 q = 1) (hb : d62939 q = 1) : d63786 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54864, d62939, d63786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54864, d62939, d63786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54865 q = 1) (hb : d62939 q = 1) : d63787 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54865, d63787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54865, d63787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2410 (p : Pattern) (ha : d54872 p = 1) (hb : d62939 p = 1) : d63795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d62938 q = 1) : d53656 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2232 q ha hb
    | true =>
      simp only [d292, d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2233 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d62938 q = 1) : d53657 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d62938 q = 1) : d53658 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d62938 q = 1) : d63793 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d63793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d63793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54871 q = 1) (hb : d62939 q = 1) : d63794 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54871, d62939, d63794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54871, d62939, d63794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54872 q = 1) (hb : d62939 q = 1) : d63795 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54872, d63795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54872, d63795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2411 (p : Pattern) (ha : d54878 p = 1) (hb : d62939 p = 1) : d63801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54866 q = 1) (hb : d62939 q = 1) : d63788 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54866, d63788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54866, d63788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2409 q ha hb
  have h2 (q : Pattern) (ha : d54867 q = 1) (hb : d62939 q = 1) : d63789 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54867, d63789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54867, d63789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54868 q = 1) (hb : d62939 q = 1) : d63790 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54868, d63790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54868, d63790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54869 q = 1) (hb : d62939 q = 1) : d63791 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54869, d63791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54869, d63791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54870 q = 1) (hb : d62939 q = 1) : d63792 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54870, d63792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54870, d63792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54873 q = 1) (hb : d62939 q = 1) : d63796 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54873, d63796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54873, d63796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2410 q ha hb
  have h7 (q : Pattern) (ha : d54874 q = 1) (hb : d62939 q = 1) : d63797 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54874, d63797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54874, d63797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54875 q = 1) (hb : d62939 q = 1) : d63798 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54875, d63798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54875, d63798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54876 q = 1) (hb : d62939 q = 1) : d63799 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54876, d63799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54876, d63799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54877 q = 1) (hb : d62939 q = 1) : d63800 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54877, d63800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54877, d63800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54878 q = 1) (hb : d62939 q = 1) : d63801 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54878, d63801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54878, d63801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2412 (p : Pattern) (ha : d54880 p = 1) (hb : d62939 p = 1) : d63804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d62938 q = 1) : d53681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2244 q ha hb
    | true =>
      simp only [d508, d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2245 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d62938 q = 1) : d53682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d62938 q = 1) : d53683 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d62938 q = 1) : d63802 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d63802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d63802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54879 q = 1) (hb : d62939 q = 1) : d63803 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54879, d62939, d63803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54879, d62939, d63803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54880 q = 1) (hb : d62939 q = 1) : d63804 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54880, d63804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54880, d63804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2413 (p : Pattern) (ha : d54886 p = 1) (hb : d62939 p = 1) : d63810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54881 q = 1) (hb : d62939 q = 1) : d63805 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54881, d63805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54881, d63805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2412 q ha hb
  have h2 (q : Pattern) (ha : d54882 q = 1) (hb : d62939 q = 1) : d63806 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54882, d63806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54882, d63806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54883 q = 1) (hb : d62939 q = 1) : d63807 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54883, d63807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54883, d63807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54884 q = 1) (hb : d62939 q = 1) : d63808 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54884, d63808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54884, d63808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54885 q = 1) (hb : d62939 q = 1) : d63809 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54885, d63809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54885, d63809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54886 q = 1) (hb : d62939 q = 1) : d63810 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54886, d63810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54886, d63810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2414 (p : Pattern) (ha : d54889 p = 1) (hb : d62939 p = 1) : d63814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d62938 q = 1) : d53708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2259 q ha hb
    | true =>
      simp only [d800, d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2260 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d62938 q = 1) : d53709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d62938 q = 1) : d53710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d62938 q = 1) : d63812 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d63812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d63812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54888 q = 1) (hb : d62939 q = 1) : d63813 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54888, d62939, d63813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54888, d62939, d63813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54889 q = 1) (hb : d62939 q = 1) : d63814 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54889, d63814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54889, d63814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2415 (p : Pattern) (ha : d54895 p = 1) (hb : d62939 p = 1) : d63820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54890 q = 1) (hb : d62939 q = 1) : d63815 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54890, d63815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54890, d63815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2414 q ha hb
  have h2 (q : Pattern) (ha : d54891 q = 1) (hb : d62939 q = 1) : d63816 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54891, d63816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54891, d63816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54892 q = 1) (hb : d62939 q = 1) : d63817 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54892, d63817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54892, d63817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54893 q = 1) (hb : d62939 q = 1) : d63818 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54893, d63818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54893, d63818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54894 q = 1) (hb : d62939 q = 1) : d63819 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54894, d63819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54894, d63819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54895 q = 1) (hb : d62939 q = 1) : d63820 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54895, d63820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54895, d63820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2416 (p : Pattern) (ha : d54899 p = 1) (hb : d62939 p = 1) : d63825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d62938 q = 1) : d53736 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2274 q ha hb
    | true =>
      simp only [d1179, d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2275 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d62938 q = 1) : d53737 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d62938 q = 1) : d53738 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d62938 q = 1) : d63823 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d63823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d63823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54898 q = 1) (hb : d62939 q = 1) : d63824 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54898, d62939, d63824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54898, d62939, d63824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54899 q = 1) (hb : d62939 q = 1) : d63825 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54899, d63825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54899, d63825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2417 (p : Pattern) (ha : d54905 p = 1) (hb : d62939 p = 1) : d63831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54900 q = 1) (hb : d62939 q = 1) : d63826 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54900, d63826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54900, d63826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2416 q ha hb
  have h2 (q : Pattern) (ha : d54901 q = 1) (hb : d62939 q = 1) : d63827 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54901, d63827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54901, d63827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54902 q = 1) (hb : d62939 q = 1) : d63828 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54902, d63828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54902, d63828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54903 q = 1) (hb : d62939 q = 1) : d63829 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54903, d63829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54903, d63829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54904 q = 1) (hb : d62939 q = 1) : d63830 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54904, d63830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54904, d63830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54905 q = 1) (hb : d62939 q = 1) : d63831 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54905, d63831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54905, d63831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2418 (p : Pattern) (ha : d54910 p = 1) (hb : d62939 p = 1) : d63837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d62938 q = 1) : d53765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2289 q ha hb
    | true =>
      simp only [d1640, d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2290 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d62938 q = 1) : d53766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d62938 q = 1) : d53767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d62938 q = 1) : d63835 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d63835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d63835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54909 q = 1) (hb : d62939 q = 1) : d63836 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54909, d62939, d63836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54909, d62939, d63836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54910 q = 1) (hb : d62939 q = 1) : d63837 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54910, d63837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54910, d63837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2419 (p : Pattern) (ha : d54916 p = 1) (hb : d62939 p = 1) : d63843 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54911 q = 1) (hb : d62939 q = 1) : d63838 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54911, d63838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54911, d63838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2418 q ha hb
  have h2 (q : Pattern) (ha : d54912 q = 1) (hb : d62939 q = 1) : d63839 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54912, d63839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54912, d63839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54913 q = 1) (hb : d62939 q = 1) : d63840 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54913, d63840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54913, d63840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54914 q = 1) (hb : d62939 q = 1) : d63841 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54914, d63841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54914, d63841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54915 q = 1) (hb : d62939 q = 1) : d63842 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54915, d63842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54915, d63842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54916 q = 1) (hb : d62939 q = 1) : d63843 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54916, d63843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54916, d63843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2420 (p : Pattern) (ha : d54922 p = 1) (hb : d62939 p = 1) : d63850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62938 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d62938 q = 1) : d53795 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2304 q ha hb
    | true =>
      simp only [d2123, d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2305 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d62938 q = 1) : d53796 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d62938 q = 1) : d53797 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d62938 q = 1) : d63848 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d63848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d63848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54921 q = 1) (hb : d62939 q = 1) : d63849 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54921, d62939, d63849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54921, d62939, d63849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54922 q = 1) (hb : d62939 q = 1) : d63850 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54922, d63850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54922, d63850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro2421 (p : Pattern) (ha : d54928 p = 1) (hb : d62939 p = 1) : d63856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54923 q = 1) (hb : d62939 q = 1) : d63851 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54923, d63851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54923, d63851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2420 q ha hb
  have h2 (q : Pattern) (ha : d54924 q = 1) (hb : d62939 q = 1) : d63852 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54924, d63852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54924, d63852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54925 q = 1) (hb : d62939 q = 1) : d63853 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54925, d63853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54925, d63853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54926 q = 1) (hb : d62939 q = 1) : d63854 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54926, d63854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54926, d63854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54927 q = 1) (hb : d62939 q = 1) : d63855 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54927, d63855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54927, d63855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54928 q = 1) (hb : d62939 q = 1) : d63856 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54928, d63856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54928, d63856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2422 (p : Pattern) (ha : d54934 p = 1) (hb : d62939 p = 1) : d63862 p = 1 := by
  have h0 (q : Pattern) (ha : d54887 q = 1) (hb : d62939 q = 1) : d63811 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54887, d63811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2411 q ha hb
    | true =>
      simp only [d54887, d63811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2413 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54896 q = 1) (hb : d62939 q = 1) : d63821 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54896, d63821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54896, d63821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2415 q ha hb
  have h3 (q : Pattern) (ha : d54897 q = 1) (hb : d62939 q = 1) : d63822 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54897, d63822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54897, d63822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54906 q = 1) (hb : d62939 q = 1) : d63832 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54906, d63832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54906, d63832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2417 q ha hb
  have h5 (q : Pattern) (ha : d54907 q = 1) (hb : d62939 q = 1) : d63833 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54907, d63833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54907, d63833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54908 q = 1) (hb : d62939 q = 1) : d63834 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54908, d63834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54908, d63834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54917 q = 1) (hb : d62939 q = 1) : d63844 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54917, d63844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54917, d63844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2419 q ha hb
  have h8 (q : Pattern) (ha : d54918 q = 1) (hb : d62939 q = 1) : d63845 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54918, d63845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54918, d63845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54919 q = 1) (hb : d62939 q = 1) : d63846 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54919, d63846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54919, d63846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54920 q = 1) (hb : d62939 q = 1) : d63847 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54920, d63847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54920, d63847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54929 q = 1) (hb : d62939 q = 1) : d63857 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54929, d63857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54929, d63857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2421 q ha hb
  have h12 (q : Pattern) (ha : d54930 q = 1) (hb : d62939 q = 1) : d63858 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54930, d63858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54930, d63858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54931 q = 1) (hb : d62939 q = 1) : d63859 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54931, d63859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54931, d63859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54932 q = 1) (hb : d62939 q = 1) : d63860 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54932, d63860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54932, d63860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54933 q = 1) (hb : d62939 q = 1) : d63861 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54933, d63861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54933, d63861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54934 q = 1) (hb : d62939 q = 1) : d63862 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54934, d63862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54934, d63862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2423 (p : Pattern) (ha : d54940 p = 1) (hb : d62939 p = 1) : d63868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54935 q = 1) (hb : d62939 q = 1) : d63863 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54935, d63863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2422 q ha hb
    | true =>
      simp only [d54935, d63863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54936 q = 1) (hb : d62939 q = 1) : d63864 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54936, d63864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54936, d63864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54937 q = 1) (hb : d62939 q = 1) : d63865 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54937, d63865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54937, d63865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54938 q = 1) (hb : d62939 q = 1) : d63866 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54938, d63866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54938, d63866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54939 q = 1) (hb : d62939 q = 1) : d63867 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54939, d63867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54939, d63867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54940 q = 1) (hb : d62939 q = 1) : d63868 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54940, d63868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54940, d63868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2424 (p : Pattern) (ha : d54946 p = 1) (hb : d62939 p = 1) : d63874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54941 q = 1) (hb : d62939 q = 1) : d63869 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54941, d63869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2423 q ha hb
    | true =>
      simp only [d54941, d63869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54942 q = 1) (hb : d62939 q = 1) : d63870 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54942, d63870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54942, d63870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54943 q = 1) (hb : d62939 q = 1) : d63871 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54943, d63871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54943, d63871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54944 q = 1) (hb : d62939 q = 1) : d63872 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54944, d63872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54944, d63872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54945 q = 1) (hb : d62939 q = 1) : d63873 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54945, d63873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54945, d63873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54946 q = 1) (hb : d62939 q = 1) : d63874 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54946, d63874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54946, d63874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2425 (p : Pattern) (ha : d54952 p = 1) (hb : d62939 p = 1) : d63880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54947 q = 1) (hb : d62939 q = 1) : d63875 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54947, d63875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2424 q ha hb
    | true =>
      simp only [d54947, d63875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54948 q = 1) (hb : d62939 q = 1) : d63876 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54948, d63876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54948, d63876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54949 q = 1) (hb : d62939 q = 1) : d63877 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54949, d63877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54949, d63877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54950 q = 1) (hb : d62939 q = 1) : d63878 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54950, d63878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54950, d63878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54951 q = 1) (hb : d62939 q = 1) : d63879 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54951, d63879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54951, d63879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54952 q = 1) (hb : d62939 q = 1) : d63880 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54952, d63880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54952, d63880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2426 (p : Pattern) (ha : d54958 p = 1) (hb : d62939 p = 1) : d63886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54953 q = 1) (hb : d62939 q = 1) : d63881 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54953, d63881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2425 q ha hb
    | true =>
      simp only [d54953, d63881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54954 q = 1) (hb : d62939 q = 1) : d63882 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54954, d63882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54954, d63882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54955 q = 1) (hb : d62939 q = 1) : d63883 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54955, d63883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54955, d63883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54956 q = 1) (hb : d62939 q = 1) : d63884 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54956, d63884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54956, d63884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54957 q = 1) (hb : d62939 q = 1) : d63885 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54957, d63885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54957, d63885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54958 q = 1) (hb : d62939 q = 1) : d63886 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54958, d63886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54958, d63886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2427 (p : Pattern) (ha : d54964 p = 1) (hb : d62939 p = 1) : d63892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54959 q = 1) (hb : d62939 q = 1) : d63887 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54959, d63887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2426 q ha hb
    | true =>
      simp only [d54959, d63887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54960 q = 1) (hb : d62939 q = 1) : d63888 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54960, d63888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54960, d63888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54961 q = 1) (hb : d62939 q = 1) : d63889 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54961, d63889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54961, d63889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54962 q = 1) (hb : d62939 q = 1) : d63890 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54962, d63890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54962, d63890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54963 q = 1) (hb : d62939 q = 1) : d63891 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54963, d63891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54963, d63891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54964 q = 1) (hb : d62939 q = 1) : d63892 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54964, d63892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54964, d63892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2428 (p : Pattern) (ha : d54970 p = 1) (hb : d62939 p = 1) : d63898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54965 q = 1) (hb : d62939 q = 1) : d63893 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54965, d63893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2427 q ha hb
    | true =>
      simp only [d54965, d63893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54966 q = 1) (hb : d62939 q = 1) : d63894 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54966, d63894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54966, d63894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54967 q = 1) (hb : d62939 q = 1) : d63895 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54967, d63895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54967, d63895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54968 q = 1) (hb : d62939 q = 1) : d63896 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54968, d63896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54968, d63896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54969 q = 1) (hb : d62939 q = 1) : d63897 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54969, d63897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54969, d63897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54970 q = 1) (hb : d62939 q = 1) : d63898 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54970, d63898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54970, d63898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2429 (p : Pattern) (ha : d54976 p = 1) (hb : d62939 p = 1) : d63904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54971 q = 1) (hb : d62939 q = 1) : d63899 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54971, d63899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2428 q ha hb
    | true =>
      simp only [d54971, d63899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54972 q = 1) (hb : d62939 q = 1) : d63900 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54972, d63900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54972, d63900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54973 q = 1) (hb : d62939 q = 1) : d63901 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54973, d63901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54973, d63901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54974 q = 1) (hb : d62939 q = 1) : d63902 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54974, d63902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54974, d63902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54975 q = 1) (hb : d62939 q = 1) : d63903 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54975, d63903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54975, d63903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54976 q = 1) (hb : d62939 q = 1) : d63904 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54976, d63904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54976, d63904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2430 (p : Pattern) (ha : d406 p = 1) (hb : d63318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63318 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d63310 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63313 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d50 q = 1) (hb : d63285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d63285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2325 q ha hb
    | true =>
      simp only [d50, d63285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107 q = 1) (hb : d63315 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d63315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107, d63315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d63286 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d63316 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d63316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108, d63316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d63317 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d63317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109, d63317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d63318 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d63318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d110, d63318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d406 q = 1) (hb : d63318 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2431 (p : Pattern) (ha : d63325 p = 1) (hb : d63787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d407 q = 1) (hb : d63319 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d63319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d407, d63319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2430 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63320 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53639 q = 1) (hb : d63321 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d63321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53639, d63321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53640 q = 1) (hb : d63322 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d63322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53640, d63322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63323 q = 1) (hb : d63785 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63323, d63785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63323, d63785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d63324 q = 1) (hb : d63786 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63324, d63786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63324, d63786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d63325 q = 1) (hb : d63787 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63325, d63787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63325, d63787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2432 (p : Pattern) (ha : d53655 p = 1) (hb : d63351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63351 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d63341 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63345 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d204 q = 1) (hb : d63314 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d63314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2331 q ha hb
    | true =>
      simp only [d204, d63314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2325 q ha hb
  have h5 (q : Pattern) (ha : d287 q = 1) (hb : d63346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d63346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287, d63346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d63348 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d288 q = 1) (hb : d63349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d63349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288, d63349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289 q = 1) (hb : d63350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d63350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289, d63350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d290 q = 1) (hb : d63351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d63351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290, d63351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53655 q = 1) (hb : d63351 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2433 (p : Pattern) (ha : d63358 p = 1) (hb : d63795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63337 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53656 q = 1) (hb : d63352 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d63352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53656, d63352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2432 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63353 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53657 q = 1) (hb : d63354 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d63354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53657, d63354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53658 q = 1) (hb : d63355 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d63355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53658, d63355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63356 q = 1) (hb : d63793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63356, d63793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63356, d63793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d63357 q = 1) (hb : d63794 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63357, d63794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63357, d63794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d63358 q = 1) (hb : d63795 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63358, d63795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63358, d63795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2434 (p : Pattern) (ha : d63364 p = 1) (hb : d63801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d63326 q = 1) (hb : d63788 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63326, d63788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63326, d63788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2431 q ha hb
  have h3 (q : Pattern) (ha : d63327 q = 1) (hb : d63789 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63327, d63789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63327, d63789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63328 q = 1) (hb : d63790 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63328, d63790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63328, d63790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63329 q = 1) (hb : d63791 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63329, d63791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63329, d63791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63330 q = 1) (hb : d63792 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63330, d63792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63330, d63792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63359 q = 1) (hb : d63796 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63359, d63796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63359, d63796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2433 q ha hb
  have h8 (q : Pattern) (ha : d63360 q = 1) (hb : d63797 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63360, d63797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63360, d63797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d63361 q = 1) (hb : d63798 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63361, d63798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63361, d63798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d63362 q = 1) (hb : d63799 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63362, d63799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63362, d63799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d63363 q = 1) (hb : d63800 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63363, d63800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63363, d63800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d63364 q = 1) (hb : d63801 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63364, d63801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63364, d63801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2435 (p : Pattern) (ha : d53680 p = 1) (hb : d63386 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63386 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d63376 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63379 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63380 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d502 q = 1) (hb : d63365 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d63365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2343 q ha hb
    | true =>
      simp only [d502, d63365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2341 q ha hb
  have h5 (q : Pattern) (ha : d503 q = 1) (hb : d63381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d63381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d503, d63381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d63383 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d504 q = 1) (hb : d63384 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d63384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d504, d63384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d505 q = 1) (hb : d63385 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d63385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d505, d63385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d506 q = 1) (hb : d63386 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d63386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d506, d63386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53680 q = 1) (hb : d63386 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2436 (p : Pattern) (ha : d63398 p = 1) (hb : d63804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63372 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53681 q = 1) (hb : d63387 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d63387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53681, d63387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2435 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63393 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53682 q = 1) (hb : d63394 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d63394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53682, d63394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53683 q = 1) (hb : d63395 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d63395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53683, d63395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63396 q = 1) (hb : d63802 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63396, d63802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63396, d63802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d63397 q = 1) (hb : d63803 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63397, d63803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63397, d63803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d63398 q = 1) (hb : d63804 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63398, d63804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63398, d63804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2437 (p : Pattern) (ha : d63404 p = 1) (hb : d63810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63399 q = 1) (hb : d63805 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63399, d63805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63399, d63805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2436 q ha hb
  have h2 (q : Pattern) (ha : d63400 q = 1) (hb : d63806 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63400, d63806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63400, d63806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63401 q = 1) (hb : d63807 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63401, d63807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63401, d63807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63402 q = 1) (hb : d63808 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63402, d63808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63402, d63808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63403 q = 1) (hb : d63809 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63403, d63809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63403, d63809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63404 q = 1) (hb : d63810 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63404, d63810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63404, d63810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2438 (p : Pattern) (ha : d53707 p = 1) (hb : d63427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63427 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d63417 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63420 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63421 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d794 q = 1) (hb : d63406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d63406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2355 q ha hb
    | true =>
      simp only [d794, d63406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2353 q ha hb
  have h5 (q : Pattern) (ha : d795 q = 1) (hb : d63422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d63422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d795, d63422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d63424 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d796 q = 1) (hb : d63425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d63425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d796, d63425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d797 q = 1) (hb : d63426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d63426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d797, d63426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d798 q = 1) (hb : d63427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d63427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d798, d63427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53707 q = 1) (hb : d63427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2439 (p : Pattern) (ha : d63439 p = 1) (hb : d63814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63413 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53708 q = 1) (hb : d63428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d63428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53708, d63428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2438 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63434 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53709 q = 1) (hb : d63435 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d63435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53709, d63435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53710 q = 1) (hb : d63436 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d63436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53710, d63436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63437 q = 1) (hb : d63812 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63437, d63812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63437, d63812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d63438 q = 1) (hb : d63813 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63438, d63813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63438, d63813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d63439 q = 1) (hb : d63814 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63439, d63814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63439, d63814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2440 (p : Pattern) (ha : d63445 p = 1) (hb : d63820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63440 q = 1) (hb : d63815 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63440, d63815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63440, d63815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2439 q ha hb
  have h2 (q : Pattern) (ha : d63441 q = 1) (hb : d63816 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63441, d63816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63441, d63816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63442 q = 1) (hb : d63817 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63442, d63817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63442, d63817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63443 q = 1) (hb : d63818 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63443, d63818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63443, d63818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63444 q = 1) (hb : d63819 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63444, d63819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63444, d63819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63445 q = 1) (hb : d63820 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63445, d63820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63445, d63820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2441 (p : Pattern) (ha : d53735 p = 1) (hb : d63469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63469 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d63459 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63462 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63463 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1173 q = 1) (hb : d63448 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d63448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2367 q ha hb
    | true =>
      simp only [d1173, d63448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2365 q ha hb
  have h5 (q : Pattern) (ha : d1174 q = 1) (hb : d63464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d63464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1174, d63464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d63466 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1175 q = 1) (hb : d63467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d63467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1175, d63467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1176 q = 1) (hb : d63468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d63468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1176, d63468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1177 q = 1) (hb : d63469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d63469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1177, d63469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53735 q = 1) (hb : d63469 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2442 (p : Pattern) (ha : d63481 p = 1) (hb : d63825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63455 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53736 q = 1) (hb : d63470 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d63470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53736, d63470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2441 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63476 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53737 q = 1) (hb : d63477 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d63477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53737, d63477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53738 q = 1) (hb : d63478 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d63478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53738, d63478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63479 q = 1) (hb : d63823 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63479, d63823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63479, d63823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d63480 q = 1) (hb : d63824 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63480, d63824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63480, d63824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d63481 q = 1) (hb : d63825 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63481, d63825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63481, d63825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2443 (p : Pattern) (ha : d63487 p = 1) (hb : d63831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63482 q = 1) (hb : d63826 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63482, d63826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63482, d63826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2442 q ha hb
  have h2 (q : Pattern) (ha : d63483 q = 1) (hb : d63827 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63483, d63827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63483, d63827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63484 q = 1) (hb : d63828 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63484, d63828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63484, d63828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63485 q = 1) (hb : d63829 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63485, d63829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63485, d63829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63486 q = 1) (hb : d63830 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63486, d63830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63486, d63830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63487 q = 1) (hb : d63831 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63487, d63831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63487, d63831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2444 (p : Pattern) (ha : d53764 p = 1) (hb : d63512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63512 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d63502 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63505 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63506 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1634 q = 1) (hb : d63491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d63491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2379 q ha hb
    | true =>
      simp only [d1634, d63491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2377 q ha hb
  have h5 (q : Pattern) (ha : d1635 q = 1) (hb : d63507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d63507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1635, d63507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d63509 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1636 q = 1) (hb : d63510 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d63510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1636, d63510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1637 q = 1) (hb : d63511 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d63511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1637, d63511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1638 q = 1) (hb : d63512 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d63512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1638, d63512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53764 q = 1) (hb : d63512 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2445 (p : Pattern) (ha : d63524 p = 1) (hb : d63837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63498 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53765 q = 1) (hb : d63513 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d63513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53765, d63513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2444 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63519 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53766 q = 1) (hb : d63520 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d63520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53766, d63520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53767 q = 1) (hb : d63521 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d63521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53767, d63521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63522 q = 1) (hb : d63835 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63522, d63835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63522, d63835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d63523 q = 1) (hb : d63836 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63523, d63836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63523, d63836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d63524 q = 1) (hb : d63837 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63524, d63837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63524, d63837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2446 (p : Pattern) (ha : d63530 p = 1) (hb : d63843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63525 q = 1) (hb : d63838 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63525, d63838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63525, d63838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2445 q ha hb
  have h2 (q : Pattern) (ha : d63526 q = 1) (hb : d63839 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63526, d63839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63526, d63839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63527 q = 1) (hb : d63840 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63527, d63840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63527, d63840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63528 q = 1) (hb : d63841 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63528, d63841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63528, d63841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63529 q = 1) (hb : d63842 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63529, d63842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63529, d63842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63530 q = 1) (hb : d63843 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63530, d63843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63530, d63843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2447 (p : Pattern) (ha : d53794 p = 1) (hb : d63556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63556 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d63546 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63550 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2117 q = 1) (hb : d63535 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d63535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2391 q ha hb
    | true =>
      simp only [d2117, d63535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2389 q ha hb
  have h5 (q : Pattern) (ha : d2118 q = 1) (hb : d63551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d63551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2118, d63551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d63553 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2119 q = 1) (hb : d63554 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d63554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2119, d63554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2120 q = 1) (hb : d63555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d63555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2120, d63555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2121 q = 1) (hb : d63556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d63556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2121, d63556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53794 q = 1) (hb : d63556 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2448 (p : Pattern) (ha : d63568 p = 1) (hb : d63850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63542 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53795 q = 1) (hb : d63557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d63557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53795, d63557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2447 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63563 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53796 q = 1) (hb : d63564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d63564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53796, d63564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53797 q = 1) (hb : d63565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d63565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53797, d63565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63566 q = 1) (hb : d63848 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63566, d63848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63566, d63848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d63567 q = 1) (hb : d63849 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63567, d63849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63567, d63849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d63568 q = 1) (hb : d63850 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63568, d63850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63568, d63850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro2449 (p : Pattern) (ha : d63574 p = 1) (hb : d63856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63569 q = 1) (hb : d63851 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63569, d63851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63569, d63851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2448 q ha hb
  have h2 (q : Pattern) (ha : d63570 q = 1) (hb : d63852 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63570, d63852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63570, d63852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63571 q = 1) (hb : d63853 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63571, d63853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63571, d63853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63572 q = 1) (hb : d63854 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63572, d63854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63572, d63854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63573 q = 1) (hb : d63855 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63573, d63855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63573, d63855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63574 q = 1) (hb : d63856 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63574, d63856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d63574, d63856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2450 (p : Pattern) (ha : d63580 p = 1) (hb : d63862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d63405 q = 1) (hb : d63811 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63405, d63811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2434 q ha hb
    | true =>
      simp only [d63405, d63811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2437 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d63446 q = 1) (hb : d63821 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63446, d63821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63446, d63821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2440 q ha hb
  have h3 (q : Pattern) (ha : d63447 q = 1) (hb : d63822 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63447, d63822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63447, d63822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63488 q = 1) (hb : d63832 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63488, d63832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63488, d63832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2443 q ha hb
  have h5 (q : Pattern) (ha : d63489 q = 1) (hb : d63833 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63489, d63833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63489, d63833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63490 q = 1) (hb : d63834 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d63490, d63834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63490, d63834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63531 q = 1) (hb : d63844 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63531, d63844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63531, d63844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2446 q ha hb
  have h8 (q : Pattern) (ha : d63532 q = 1) (hb : d63845 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63532, d63845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63532, d63845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d63533 q = 1) (hb : d63846 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d63533, d63846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63533, d63846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d63534 q = 1) (hb : d63847 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d63534, d63847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63534, d63847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d63575 q = 1) (hb : d63857 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63575, d63857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63575, d63857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2449 q ha hb
  have h12 (q : Pattern) (ha : d63576 q = 1) (hb : d63858 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63576, d63858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63576, d63858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d63577 q = 1) (hb : d63859 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d63577, d63859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63577, d63859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d63578 q = 1) (hb : d63860 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d63578, d63860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d63578, d63860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d63579 q = 1) (hb : d63861 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d63579, d63861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d63579, d63861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d63580 q = 1) (hb : d63862 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d63580, d63862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d63580, d63862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro2451 (p : Pattern) (ha : d63586 p = 1) (hb : d63868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63581 q = 1) (hb : d63863 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d63581, d63863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2450 q ha hb
    | true =>
      simp only [d63581, d63863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63582 q = 1) (hb : d63864 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d63582, d63864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63582, d63864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63583 q = 1) (hb : d63865 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d63583, d63865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63583, d63865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63584 q = 1) (hb : d63866 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d63584, d63866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63584, d63866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63585 q = 1) (hb : d63867 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d63585, d63867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63585, d63867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63586 q = 1) (hb : d63868 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d63586, d63868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63586, d63868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2452 (p : Pattern) (ha : d63592 p = 1) (hb : d63874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63587 q = 1) (hb : d63869 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d63587, d63869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2451 q ha hb
    | true =>
      simp only [d63587, d63869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63588 q = 1) (hb : d63870 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d63588, d63870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63588, d63870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63589 q = 1) (hb : d63871 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d63589, d63871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63589, d63871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63590 q = 1) (hb : d63872 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d63590, d63872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63590, d63872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63591 q = 1) (hb : d63873 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d63591, d63873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63591, d63873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63592 q = 1) (hb : d63874 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d63592, d63874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63592, d63874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2453 (p : Pattern) (ha : d63598 p = 1) (hb : d63880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63593 q = 1) (hb : d63875 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d63593, d63875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2452 q ha hb
    | true =>
      simp only [d63593, d63875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63594 q = 1) (hb : d63876 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d63594, d63876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63594, d63876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63595 q = 1) (hb : d63877 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d63595, d63877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63595, d63877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63596 q = 1) (hb : d63878 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d63596, d63878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63596, d63878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63597 q = 1) (hb : d63879 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d63597, d63879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63597, d63879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63598 q = 1) (hb : d63880 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d63598, d63880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63598, d63880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2454 (p : Pattern) (ha : d63604 p = 1) (hb : d63886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63599 q = 1) (hb : d63881 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d63599, d63881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2453 q ha hb
    | true =>
      simp only [d63599, d63881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63600 q = 1) (hb : d63882 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d63600, d63882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63600, d63882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63601 q = 1) (hb : d63883 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d63601, d63883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63601, d63883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63602 q = 1) (hb : d63884 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d63602, d63884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63602, d63884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63603 q = 1) (hb : d63885 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d63603, d63885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63603, d63885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63604 q = 1) (hb : d63886 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d63604, d63886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63604, d63886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2455 (p : Pattern) (ha : d63610 p = 1) (hb : d63892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63605 q = 1) (hb : d63887 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d63605, d63887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2454 q ha hb
    | true =>
      simp only [d63605, d63887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63606 q = 1) (hb : d63888 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d63606, d63888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63606, d63888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63607 q = 1) (hb : d63889 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d63607, d63889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63607, d63889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63608 q = 1) (hb : d63890 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d63608, d63890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63608, d63890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63609 q = 1) (hb : d63891 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d63609, d63891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63609, d63891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63610 q = 1) (hb : d63892 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d63610, d63892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63610, d63892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2456 (p : Pattern) (ha : d63616 p = 1) (hb : d63898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63611 q = 1) (hb : d63893 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d63611, d63893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2455 q ha hb
    | true =>
      simp only [d63611, d63893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63612 q = 1) (hb : d63894 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d63612, d63894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63612, d63894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63613 q = 1) (hb : d63895 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d63613, d63895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63613, d63895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63614 q = 1) (hb : d63896 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d63614, d63896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63614, d63896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63615 q = 1) (hb : d63897 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d63615, d63897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63615, d63897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63616 q = 1) (hb : d63898 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d63616, d63898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63616, d63898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2457 (p : Pattern) (ha : d63622 p = 1) (hb : d63904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63617 q = 1) (hb : d63899 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d63617, d63899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2456 q ha hb
    | true =>
      simp only [d63617, d63899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d63618 q = 1) (hb : d63900 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d63618, d63900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63618, d63900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d63619 q = 1) (hb : d63901 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d63619, d63901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63619, d63901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d63620 q = 1) (hb : d63902 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d63620, d63902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63620, d63902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d63621 q = 1) (hb : d63903 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d63621, d63903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63621, d63903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d63622 q = 1) (hb : d63904 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d63622, d63904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63622, d63904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2458 (p : Pattern) (ha : d406 p = 1) (hb : d63908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d62968 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d62969 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107 q = 1) (hb : d63905 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d63905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107, d63905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d62941 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108 q = 1) (hb : d63906 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d63906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108, d63906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109 q = 1) (hb : d63907 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d63907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109, d63907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d110 q = 1) (hb : d63908 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d63908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d110, d63908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d406 q = 1) (hb : d63908 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2459 (p : Pattern) (ha : d63787 p = 1) (hb : d63914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62961 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d407 q = 1) (hb : d63909 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d63909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d407, d63909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2458 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d62976 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53639 q = 1) (hb : d63910 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d63910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53639, d63910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53640 q = 1) (hb : d63911 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d63911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53640, d63911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63785 q = 1) (hb : d63912 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63785, d63912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63785, d63912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63786 q = 1) (hb : d63913 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63786, d63913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63786, d63913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d63787 q = 1) (hb : d63914 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63787, d63914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63787, d63914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2460 (p : Pattern) (ha : d53655 p = 1) (hb : d63923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63923 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62997 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63000 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63001 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287 q = 1) (hb : d63920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d63920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287, d63920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d63005 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d288 q = 1) (hb : d63921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d63921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288, d63921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289 q = 1) (hb : d63922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d63922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289, d63922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d290 q = 1) (hb : d63923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d63923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290, d63923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53655 q = 1) (hb : d63923 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2461 (p : Pattern) (ha : d63795 p = 1) (hb : d63929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62993 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53656 q = 1) (hb : d63924 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d63924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53656, d63924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2460 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63010 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53657 q = 1) (hb : d63925 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d63925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53657, d63925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53658 q = 1) (hb : d63926 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d63926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53658, d63926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63793 q = 1) (hb : d63927 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63793, d63927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63793, d63927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63794 q = 1) (hb : d63928 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63794, d63928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63794, d63928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d63795 q = 1) (hb : d63929 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63795, d63929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63795, d63929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2462 (p : Pattern) (ha : d63801 p = 1) (hb : d63935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62954 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d63788 q = 1) (hb : d63915 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63788, d63915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63788, d63915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2459 q ha hb
  have h3 (q : Pattern) (ha : d63789 q = 1) (hb : d63916 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63789, d63916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63789, d63916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63790 q = 1) (hb : d63917 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63790, d63917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63790, d63917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63791 q = 1) (hb : d63918 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63791, d63918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63791, d63918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63792 q = 1) (hb : d63919 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63792, d63919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63792, d63919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63796 q = 1) (hb : d63930 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63796, d63930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63796, d63930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2461 q ha hb
  have h8 (q : Pattern) (ha : d63797 q = 1) (hb : d63931 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63797, d63931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63797, d63931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d63798 q = 1) (hb : d63932 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63798, d63932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63798, d63932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d63799 q = 1) (hb : d63933 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63799, d63933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63799, d63933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d63800 q = 1) (hb : d63934 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63800, d63934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63800, d63934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d63801 q = 1) (hb : d63935 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63801, d63935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63801, d63935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2463 (p : Pattern) (ha : d53680 p = 1) (hb : d63939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d63033 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63036 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63037 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d502 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d503 q = 1) (hb : d63936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d63936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d503, d63936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d63041 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d504 q = 1) (hb : d63937 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d63937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d504, d63937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d505 q = 1) (hb : d63938 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d63938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d505, d63938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d506 q = 1) (hb : d63939 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d63939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d506, d63939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53680 q = 1) (hb : d63939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2464 (p : Pattern) (ha : d63804 p = 1) (hb : d63945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63029 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53681 q = 1) (hb : d63940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d63940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53681, d63940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2463 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63051 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53682 q = 1) (hb : d63941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d63941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53682, d63941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53683 q = 1) (hb : d63942 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d63942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53683, d63942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63802 q = 1) (hb : d63943 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63802, d63943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63802, d63943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63803 q = 1) (hb : d63944 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63803, d63944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63803, d63944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d63804 q = 1) (hb : d63945 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63804, d63945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63804, d63945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2465 (p : Pattern) (ha : d63810 p = 1) (hb : d63951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63805 q = 1) (hb : d63946 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63805, d63946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63805, d63946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2464 q ha hb
  have h2 (q : Pattern) (ha : d63806 q = 1) (hb : d63947 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63806, d63947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63806, d63947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63807 q = 1) (hb : d63948 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63807, d63948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63807, d63948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63808 q = 1) (hb : d63949 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63808, d63949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63808, d63949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63809 q = 1) (hb : d63950 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63809, d63950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63809, d63950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63810 q = 1) (hb : d63951 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63810, d63951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63810, d63951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2466 (p : Pattern) (ha : d53707 p = 1) (hb : d63956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63956 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d63075 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63078 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63079 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d794 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d795 q = 1) (hb : d63953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d63953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d795, d63953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d63083 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d796 q = 1) (hb : d63954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d63954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d796, d63954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d797 q = 1) (hb : d63955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d63955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d797, d63955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d798 q = 1) (hb : d63956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d63956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d798, d63956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53707 q = 1) (hb : d63956 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2467 (p : Pattern) (ha : d63814 p = 1) (hb : d63962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63071 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53708 q = 1) (hb : d63957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d63957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53708, d63957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2466 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63093 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53709 q = 1) (hb : d63958 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d63958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53709, d63958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53710 q = 1) (hb : d63959 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d63959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53710, d63959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63812 q = 1) (hb : d63960 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63812, d63960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63812, d63960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63813 q = 1) (hb : d63961 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63813, d63961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63813, d63961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d63814 q = 1) (hb : d63962 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63814, d63962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63814, d63962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2468 (p : Pattern) (ha : d63820 p = 1) (hb : d63968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63815 q = 1) (hb : d63963 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63815, d63963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63815, d63963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2467 q ha hb
  have h2 (q : Pattern) (ha : d63816 q = 1) (hb : d63964 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63816, d63964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63816, d63964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63817 q = 1) (hb : d63965 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63817, d63965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63817, d63965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63818 q = 1) (hb : d63966 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63818, d63966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63818, d63966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63819 q = 1) (hb : d63967 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63819, d63967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63819, d63967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63820 q = 1) (hb : d63968 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63820, d63968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63820, d63968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2469 (p : Pattern) (ha : d53735 p = 1) (hb : d63974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63974 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d63118 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63122 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1173 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1174 q = 1) (hb : d63971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d63971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1174, d63971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d63126 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1175 q = 1) (hb : d63972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d63972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1175, d63972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1176 q = 1) (hb : d63973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d63973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1176, d63973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1177 q = 1) (hb : d63974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d63974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1177, d63974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53735 q = 1) (hb : d63974 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2470 (p : Pattern) (ha : d63825 p = 1) (hb : d63980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53736 q = 1) (hb : d63975 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d63975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53736, d63975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2469 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63136 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53737 q = 1) (hb : d63976 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d63976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53737, d63976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53738 q = 1) (hb : d63977 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d63977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53738, d63977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63823 q = 1) (hb : d63978 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63823, d63978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63823, d63978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63824 q = 1) (hb : d63979 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63824, d63979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63824, d63979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d63825 q = 1) (hb : d63980 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63825, d63980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63825, d63980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2471 (p : Pattern) (ha : d63831 p = 1) (hb : d63986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63826 q = 1) (hb : d63981 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63826, d63981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63826, d63981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2470 q ha hb
  have h2 (q : Pattern) (ha : d63827 q = 1) (hb : d63982 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63827, d63982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63827, d63982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63828 q = 1) (hb : d63983 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63828, d63983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63828, d63983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63829 q = 1) (hb : d63984 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63829, d63984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63829, d63984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63830 q = 1) (hb : d63985 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63830, d63985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63830, d63985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63831 q = 1) (hb : d63986 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63831, d63986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63831, d63986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2472 (p : Pattern) (ha : d53764 p = 1) (hb : d63993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63993 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d63162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63166 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1634 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1635 q = 1) (hb : d63990 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d63990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1635, d63990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d63170 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1636 q = 1) (hb : d63991 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d63991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1636, d63991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1637 q = 1) (hb : d63992 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d63992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1637, d63992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1638 q = 1) (hb : d63993 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d63993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1638, d63993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53764 q = 1) (hb : d63993 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2473 (p : Pattern) (ha : d63837 p = 1) (hb : d63999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63158 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53765 q = 1) (hb : d63994 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d63994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53765, d63994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2472 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63180 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53766 q = 1) (hb : d63995 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d63995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53766, d63995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53767 q = 1) (hb : d63996 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d63996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53767, d63996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63835 q = 1) (hb : d63997 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63835, d63997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63835, d63997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63836 q = 1) (hb : d63998 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63836, d63998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63836, d63998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d63837 q = 1) (hb : d63999 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63837, d63999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63837, d63999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2474 (p : Pattern) (ha : d63843 p = 1) (hb : d64005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63838 q = 1) (hb : d64000 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63838, d64000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63838, d64000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2473 q ha hb
  have h2 (q : Pattern) (ha : d63839 q = 1) (hb : d64001 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63839, d64001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63839, d64001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63840 q = 1) (hb : d64002 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63840, d64002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63840, d64002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63841 q = 1) (hb : d64003 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63841, d64003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63841, d64003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63842 q = 1) (hb : d64004 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63842, d64004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63842, d64004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63843 q = 1) (hb : d64005 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63843, d64005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63843, d64005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2475 (p : Pattern) (ha : d53794 p = 1) (hb : d64013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64013 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d63207 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d63210 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63211 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2117 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2118 q = 1) (hb : d64010 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d64010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2118, d64010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d63215 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2119 q = 1) (hb : d64011 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d64011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2119, d64011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2120 q = 1) (hb : d64012 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d64012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2120, d64012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2121 q = 1) (hb : d64013 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d64013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2121, d64013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53794 q = 1) (hb : d64013 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro2476 (p : Pattern) (ha : d63850 p = 1) (hb : d64019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d63203 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53795 q = 1) (hb : d64014 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d64014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53795, d64014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2475 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d63225 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53796 q = 1) (hb : d64015 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d64015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53796, d64015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53797 q = 1) (hb : d64016 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d64016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53797, d64016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d63848 q = 1) (hb : d64017 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63848, d64017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63848, d64017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63849 q = 1) (hb : d64018 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63849, d64018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63849, d64018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d63850 q = 1) (hb : d64019 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63850, d64019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d63850, d64019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro2477 (p : Pattern) (ha : d63856 p = 1) (hb : d64025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63851 q = 1) (hb : d64020 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63851, d64020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63851, d64020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2476 q ha hb
  have h2 (q : Pattern) (ha : d63852 q = 1) (hb : d64021 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63852, d64021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63852, d64021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d63853 q = 1) (hb : d64022 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63853, d64022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63853, d64022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63854 q = 1) (hb : d64023 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63854, d64023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63854, d64023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d63855 q = 1) (hb : d64024 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63855, d64024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63855, d64024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63856 q = 1) (hb : d64025 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63856, d64025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63856, d64025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2478 (p : Pattern) (ha : d63862 p = 1) (hb : d64031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d63811 q = 1) (hb : d63952 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63811, d63952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2462 q ha hb
    | true =>
      simp only [d63811, d63952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2465 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d63821 q = 1) (hb : d63969 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63821, d63969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63821, d63969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2468 q ha hb
  have h3 (q : Pattern) (ha : d63822 q = 1) (hb : d63970 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63822, d63970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d63822, d63970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d63832 q = 1) (hb : d63987 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63832, d63987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63832, d63987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2471 q ha hb
  have h5 (q : Pattern) (ha : d63833 q = 1) (hb : d63988 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63833, d63988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63833, d63988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d63834 q = 1) (hb : d63989 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d63834, d63989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63834, d63989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d63844 q = 1) (hb : d64006 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63844, d64006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63844, d64006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2474 q ha hb
  have h8 (q : Pattern) (ha : d63845 q = 1) (hb : d64007 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63845, d64007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63845, d64007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d63846 q = 1) (hb : d64008 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d63846, d64008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63846, d64008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d63847 q = 1) (hb : d64009 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d63847, d64009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63847, d64009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d63857 q = 1) (hb : d64026 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63857, d64026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63857, d64026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2477 q ha hb
  have h12 (q : Pattern) (ha : d63858 q = 1) (hb : d64027 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63858, d64027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63858, d64027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d63859 q = 1) (hb : d64028 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d63859, d64028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63859, d64028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d63860 q = 1) (hb : d64029 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d63860, d64029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63860, d64029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d63861 q = 1) (hb : d64030 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d63861, d64030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d63861, d64030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d63862 q = 1) (hb : d64031 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d63862, d64031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d63862, d64031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2479 (p : Pattern) (ha : d63868 p = 1) (hb : d64037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63863 q = 1) (hb : d64032 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d63863, d64032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2478 q ha hb
    | true =>
      simp only [d63863, d64032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d63864 q = 1) (hb : d64033 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d63864, d64033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63864, d64033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63865 q = 1) (hb : d64034 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d63865, d64034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63865, d64034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d63866 q = 1) (hb : d64035 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d63866, d64035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63866, d64035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d63867 q = 1) (hb : d64036 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d63867, d64036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63867, d64036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d63868 q = 1) (hb : d64037 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d63868, d64037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63868, d64037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2480 (p : Pattern) (ha : d63874 p = 1) (hb : d64043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63869 q = 1) (hb : d64038 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d63869, d64038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2479 q ha hb
    | true =>
      simp only [d63869, d64038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d63870 q = 1) (hb : d64039 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d63870, d64039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63870, d64039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63871 q = 1) (hb : d64040 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d63871, d64040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63871, d64040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d63872 q = 1) (hb : d64041 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d63872, d64041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63872, d64041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d63873 q = 1) (hb : d64042 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d63873, d64042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63873, d64042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d63874 q = 1) (hb : d64043 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d63874, d64043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63874, d64043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2481 (p : Pattern) (ha : d63880 p = 1) (hb : d64049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63875 q = 1) (hb : d64044 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d63875, d64044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2480 q ha hb
    | true =>
      simp only [d63875, d64044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d63876 q = 1) (hb : d64045 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d63876, d64045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63876, d64045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63877 q = 1) (hb : d64046 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d63877, d64046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63877, d64046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d63878 q = 1) (hb : d64047 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d63878, d64047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63878, d64047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d63879 q = 1) (hb : d64048 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d63879, d64048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63879, d64048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d63880 q = 1) (hb : d64049 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d63880, d64049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63880, d64049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2482 (p : Pattern) (ha : d63886 p = 1) (hb : d64055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63881 q = 1) (hb : d64050 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d63881, d64050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2481 q ha hb
    | true =>
      simp only [d63881, d64050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d63882 q = 1) (hb : d64051 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d63882, d64051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63882, d64051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63883 q = 1) (hb : d64052 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d63883, d64052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63883, d64052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d63884 q = 1) (hb : d64053 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d63884, d64053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63884, d64053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d63885 q = 1) (hb : d64054 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d63885, d64054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63885, d64054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d63886 q = 1) (hb : d64055 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d63886, d64055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63886, d64055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2483 (p : Pattern) (ha : d63892 p = 1) (hb : d64061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63887 q = 1) (hb : d64056 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d63887, d64056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2482 q ha hb
    | true =>
      simp only [d63887, d64056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d63888 q = 1) (hb : d64057 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d63888, d64057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63888, d64057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63889 q = 1) (hb : d64058 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d63889, d64058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63889, d64058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d63890 q = 1) (hb : d64059 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d63890, d64059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63890, d64059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d63891 q = 1) (hb : d64060 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d63891, d64060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63891, d64060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d63892 q = 1) (hb : d64061 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d63892, d64061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63892, d64061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2484 (p : Pattern) (ha : d63898 p = 1) (hb : d64067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63893 q = 1) (hb : d64062 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d63893, d64062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2483 q ha hb
    | true =>
      simp only [d63893, d64062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d63894 q = 1) (hb : d64063 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d63894, d64063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63894, d64063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63895 q = 1) (hb : d64064 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d63895, d64064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63895, d64064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d63896 q = 1) (hb : d64065 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d63896, d64065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63896, d64065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d63897 q = 1) (hb : d64066 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d63897, d64066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63897, d64066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d63898 q = 1) (hb : d64067 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d63898, d64067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63898, d64067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2485 (p : Pattern) (ha : d63904 p = 1) (hb : d64073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d63899 q = 1) (hb : d64068 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d63899, d64068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2484 q ha hb
    | true =>
      simp only [d63899, d64068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d63900 q = 1) (hb : d64069 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d63900, d64069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d63900, d64069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d63901 q = 1) (hb : d64070 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d63901, d64070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d63901, d64070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d63902 q = 1) (hb : d64071 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d63902, d64071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63902, d64071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d63903 q = 1) (hb : d64072 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d63903, d64072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d63903, d64072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d63904 q = 1) (hb : d64073 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d63904, d64073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d63904, d64073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2486 (p : Pattern) (ha : d2520 p = 1) (hb : d55755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d59 q = 1) (hb : d55754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, d55754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2519 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2519, d55755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2519, d55755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2520 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2487 (p : Pattern) (ha : d54752 p = 1) (hb : d55755 p = 1) : d64075 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d114 q = 1) : d114 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51649 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51650 q = 1) (hb : d55754 q = 1) : d2896 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d55754, d2896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51650, d55754, d2896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54751 q = 1) (hb : d55755 q = 1) : d64074 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54751, d55755, d64074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54751, d55755, d64074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54752 q = 1) (hb : d55755 q = 1) : d64075 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54752, d64075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54752, d64075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2488 (p : Pattern) (ha : d54759 p = 1) (hb : d55755 p = 1) : d64082 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d294 q = 1) : d294 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51666 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51667 q = 1) (hb : d55754 q = 1) : d2904 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d55754, d2904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51667, d55754, d2904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54758 q = 1) (hb : d55755 q = 1) : d64081 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54758, d55755, d64081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54758, d55755, d64081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54759 q = 1) (hb : d55755 q = 1) : d64082 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54759, d64082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54759, d64082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2489 (p : Pattern) (ha : d54765 p = 1) (hb : d55755 p = 1) : d64088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2521 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2486 q ha hb
  have h2 (q : Pattern) (ha : d2522 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2523 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2524 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54753 q = 1) (hb : d55755 q = 1) : d64076 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54753, d64076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54753, d64076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2487 q ha hb
  have h6 (q : Pattern) (ha : d54754 q = 1) (hb : d55755 q = 1) : d64077 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54754, d64077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54754, d64077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54755 q = 1) (hb : d55755 q = 1) : d64078 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54755, d64078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54755, d64078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54756 q = 1) (hb : d55755 q = 1) : d64079 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54756, d64079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54756, d64079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54757 q = 1) (hb : d55755 q = 1) : d64080 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54757, d64080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54757, d64080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54760 q = 1) (hb : d55755 q = 1) : d64083 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54760, d64083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54760, d64083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2488 q ha hb
  have h11 (q : Pattern) (ha : d54761 q = 1) (hb : d55755 q = 1) : d64084 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54761, d64084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54761, d64084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54762 q = 1) (hb : d55755 q = 1) : d64085 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54762, d64085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54762, d64085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54763 q = 1) (hb : d55755 q = 1) : d64086 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54763, d64086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54763, d64086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54764 q = 1) (hb : d55755 q = 1) : d64087 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54764, d64087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54764, d64087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54765 q = 1) (hb : d55755 q = 1) : d64088 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54765, d64088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54765, d64088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro2490 (p : Pattern) (ha : d54767 p = 1) (hb : d55755 p = 1) : d64090 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d510 q = 1) : d510 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51691 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51692 q = 1) (hb : d55754 q = 1) : d2913 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d55754, d2913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51692, d55754, d2913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54766 q = 1) (hb : d55755 q = 1) : d64089 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54766, d55755, d64089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54766, d55755, d64089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54767 q = 1) (hb : d55755 q = 1) : d64090 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54767, d64090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54767, d64090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2491 (p : Pattern) (ha : d54773 p = 1) (hb : d55755 p = 1) : d64096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54768 q = 1) (hb : d55755 q = 1) : d64091 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54768, d64091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54768, d64091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2490 q ha hb
  have h2 (q : Pattern) (ha : d54769 q = 1) (hb : d55755 q = 1) : d64092 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54769, d64092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54769, d64092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54770 q = 1) (hb : d55755 q = 1) : d64093 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54770, d64093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54770, d64093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54771 q = 1) (hb : d55755 q = 1) : d64094 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54771, d64094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54771, d64094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54772 q = 1) (hb : d55755 q = 1) : d64095 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54772, d64095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54772, d64095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54773 q = 1) (hb : d55755 q = 1) : d64096 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54773, d64096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54773, d64096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2492 (p : Pattern) (ha : d54776 p = 1) (hb : d55755 p = 1) : d64099 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d802 q = 1) : d802 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51718 q = 1) (hb : d55754 q = 1) : d2923 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d55754, d2923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51718, d55754, d2923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54775 q = 1) (hb : d55755 q = 1) : d64098 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54775, d55755, d64098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54775, d55755, d64098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54776 q = 1) (hb : d55755 q = 1) : d64099 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54776, d64099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54776, d64099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2493 (p : Pattern) (ha : d54782 p = 1) (hb : d55755 p = 1) : d64105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54777 q = 1) (hb : d55755 q = 1) : d64100 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54777, d64100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54777, d64100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2492 q ha hb
  have h2 (q : Pattern) (ha : d54778 q = 1) (hb : d55755 q = 1) : d64101 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54778, d64101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54778, d64101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54779 q = 1) (hb : d55755 q = 1) : d64102 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54779, d64102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54779, d64102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54780 q = 1) (hb : d55755 q = 1) : d64103 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54780, d64103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54780, d64103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54781 q = 1) (hb : d55755 q = 1) : d64104 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54781, d64104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54781, d64104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54782 q = 1) (hb : d55755 q = 1) : d64105 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54782, d64105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54782, d64105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2494 (p : Pattern) (ha : d54786 p = 1) (hb : d55755 p = 1) : d64109 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1181 q = 1) : d1181 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51744 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51745 q = 1) (hb : d55754 q = 1) : d2934 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d55754, d2934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51745, d55754, d2934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54785 q = 1) (hb : d55755 q = 1) : d64108 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54785, d55755, d64108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54785, d55755, d64108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54786 q = 1) (hb : d55755 q = 1) : d64109 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54786, d64109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54786, d64109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2495 (p : Pattern) (ha : d54792 p = 1) (hb : d55755 p = 1) : d64115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54787 q = 1) (hb : d55755 q = 1) : d64110 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54787, d64110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54787, d64110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2494 q ha hb
  have h2 (q : Pattern) (ha : d54788 q = 1) (hb : d55755 q = 1) : d64111 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54788, d64111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54788, d64111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54789 q = 1) (hb : d55755 q = 1) : d64112 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54789, d64112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54789, d64112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54790 q = 1) (hb : d55755 q = 1) : d64113 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54790, d64113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54790, d64113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54791 q = 1) (hb : d55755 q = 1) : d64114 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54791, d64114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54791, d64114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54792 q = 1) (hb : d55755 q = 1) : d64115 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54792, d64115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54792, d64115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2496 (p : Pattern) (ha : d54797 p = 1) (hb : d55755 p = 1) : d64120 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1642 q = 1) : d1642 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51772 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51773 q = 1) (hb : d55754 q = 1) : d2946 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d55754, d2946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51773, d55754, d2946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54796 q = 1) (hb : d55755 q = 1) : d64119 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54796, d55755, d64119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54796, d55755, d64119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54797 q = 1) (hb : d55755 q = 1) : d64120 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54797, d64120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54797, d64120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2497 (p : Pattern) (ha : d54803 p = 1) (hb : d55755 p = 1) : d64126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54798 q = 1) (hb : d55755 q = 1) : d64121 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54798, d64121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54798, d64121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2496 q ha hb
  have h2 (q : Pattern) (ha : d54799 q = 1) (hb : d55755 q = 1) : d64122 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54799, d64122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54799, d64122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54800 q = 1) (hb : d55755 q = 1) : d64123 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54800, d64123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54800, d64123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54801 q = 1) (hb : d55755 q = 1) : d64124 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54801, d64124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54801, d64124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54802 q = 1) (hb : d55755 q = 1) : d64125 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54802, d64125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54802, d64125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54803 q = 1) (hb : d55755 q = 1) : d64126 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54803, d64126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54803, d64126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2498 (p : Pattern) (ha : d54809 p = 1) (hb : d55755 p = 1) : d64132 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2125 q = 1) : d2125 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51802 q = 1) (hb : d55754 q = 1) : d2959 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d55754, d2959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51802, d55754, d2959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54808 q = 1) (hb : d55755 q = 1) : d64131 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54808, d55755, d64131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54808, d55755, d64131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54809 q = 1) (hb : d55755 q = 1) : d64132 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54809, d64132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54809, d64132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2499 (p : Pattern) (ha : d54815 p = 1) (hb : d55755 p = 1) : d64138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54810 q = 1) (hb : d55755 q = 1) : d64133 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54810, d64133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54810, d64133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2498 q ha hb
  have h2 (q : Pattern) (ha : d54811 q = 1) (hb : d55755 q = 1) : d64134 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54811, d64134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54811, d64134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54812 q = 1) (hb : d55755 q = 1) : d64135 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54812, d64135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54812, d64135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54813 q = 1) (hb : d55755 q = 1) : d64136 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54813, d64136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54813, d64136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54814 q = 1) (hb : d55755 q = 1) : d64137 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54814, d64137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54814, d64137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54815 q = 1) (hb : d55755 q = 1) : d64138 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54815, d64138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54815, d64138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
