import NetHack.Soko22Hazard87.AndIntroBlocks0416
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro104250 (p : Pattern) (ha : d269204 p = 1) (hb : d324732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269109 q = 1) (hb : d324679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269109, d324679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104233 q ha hb
    | true =>
      simp only [d269109, d324679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104234 q ha hb
  have h2 (q : Pattern) (ha : d269110 q = 1) (hb : d324680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269110, d324680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269110, d324680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269111 q = 1) (hb : d324681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269111, d324681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269111, d324681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269112 q = 1) (hb : d324682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269112, d324682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269112, d324682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269119 q = 1) (hb : d324689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269119, d324689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104235 q ha hb
    | true =>
      simp only [d269119, d324689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104236 q ha hb
  have h6 (q : Pattern) (ha : d269120 q = 1) (hb : d324690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269120, d324690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269120, d324690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269121 q = 1) (hb : d324691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269121, d324691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269121, d324691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269171 q = 1) (hb : d324705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269171, d324705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104242 q ha hb
    | true =>
      simp only [d269171, d324705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104243 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269086 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d269172 q = 1) (hb : d324706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269172, d324706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269172, d324706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d269199 q = 1) (hb : d324727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269199, d324727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104249 q ha hb
    | true =>
      simp only [d269199, d324727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269200 q = 1) (hb : d324728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269200, d324728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269200, d324728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269201 q = 1) (hb : d324729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269201, d324729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269201, d324729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269202 q = 1) (hb : d324730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269202, d324730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269202, d324730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269203 q = 1) (hb : d324731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269203, d324731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269203, d324731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269204 q = 1) (hb : d324732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269204, d324732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269204, d324732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro104251 (p : Pattern) (ha : d269205 p = 1) (hb : d324733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269072 q = 1) (hb : d324642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269072, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104225 q ha hb
    | true =>
      simp only [d269072, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269073 q = 1) (hb : d324643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269073, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269073, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269076 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104226 q ha hb
    | true =>
      simp only [d269076, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269077 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269078 q = 1) (hb : d324648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269078, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269078, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269079 q = 1) (hb : d324649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269079, d324649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269079, d324649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269105 q = 1) (hb : d324675 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269105, d324675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269105, d324675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269205 q = 1) (hb : d324733 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269205, d324733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269205, d324733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104252 (p : Pattern) (ha : d269206 p = 1) (hb : d324734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269076 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104226 q ha hb
    | true =>
      simp only [d269076, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269077 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269082 q = 1) (hb : d324652 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269082, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269082, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269083 q = 1) (hb : d324653 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269083, d324653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269083, d324653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269107 q = 1) (hb : d324677 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269107, d324677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269107, d324677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269206 q = 1) (hb : d324734 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269206, d324734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269206, d324734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104253 (p : Pattern) (ha : d269211 p = 1) (hb : d324739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269072 q = 1) (hb : d324642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269072, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104225 q ha hb
    | true =>
      simp only [d269072, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269073 q = 1) (hb : d324643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269073, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269073, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269076 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104226 q ha hb
    | true =>
      simp only [d269076, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269077 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269078 q = 1) (hb : d324648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269078, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269078, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269113 q = 1) (hb : d324683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269113, d324683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269113, d324683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269114 q = 1) (hb : d324684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269114, d324684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269114, d324684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269211 q = 1) (hb : d324739 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269211, d324739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269211, d324739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104254 (p : Pattern) (ha : d269212 p = 1) (hb : d324740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269076 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104226 q ha hb
    | true =>
      simp only [d269076, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269077 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269082 q = 1) (hb : d324652 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269082, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269082, d324652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269116 q = 1) (hb : d324686 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269116, d324686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269116, d324686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269117 q = 1) (hb : d324687 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269117, d324687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269117, d324687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269212 q = 1) (hb : d324740 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269212, d324740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269212, d324740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104255 (p : Pattern) (ha : d269216 p = 1) (hb : d324744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269156 q = 1) (hb : d324699 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269156, d324699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104240 q ha hb
    | true =>
      simp only [d269156, d324699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269157 q = 1) (hb : d324700 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269157, d324700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269157, d324700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269161 q = 1) (hb : d324642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269161, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104241 q ha hb
    | true =>
      simp only [d269161, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269162 q = 1) (hb : d324643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269162, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269162, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269163 q = 1) (hb : d324701 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269163, d324701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269163, d324701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269164 q = 1) (hb : d324702 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269164, d324702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269164, d324702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269165 q = 1) (hb : d324703 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269165, d324703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269165, d324703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269216 q = 1) (hb : d324744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269216, d324744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269216, d324744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104256 (p : Pattern) (ha : d269217 p = 1) (hb : d324664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269161 q = 1) (hb : d324642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269161, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104241 q ha hb
    | true =>
      simp only [d269161, d324642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269162 q = 1) (hb : d324643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269162, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269162, d324643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269076 q = 1) (hb : d324646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269076, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104226 q ha hb
    | true =>
      simp only [d269076, d324646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269077 q = 1) (hb : d324647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269077, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269077, d324647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269167 q = 1) (hb : d324648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269167, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269167, d324648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269168 q = 1) (hb : d324649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269168, d324649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269168, d324649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269169 q = 1) (hb : d324650 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269169, d324650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269169, d324650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269217 q = 1) (hb : d324664 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269217, d324664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269217, d324664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104257 (p : Pattern) (ha : d269220 p = 1) (hb : d324747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269193 q = 1) (hb : d324721 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269193, d324721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104248 q ha hb
    | true =>
      simp only [d269193, d324721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269194 q = 1) (hb : d324722 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269194, d324722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269194, d324722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269195 q = 1) (hb : d324723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269195, d324723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269195, d324723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269196 q = 1) (hb : d324724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269196, d324724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269196, d324724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269197 q = 1) (hb : d324725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269197, d324725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269197, d324725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269220 q = 1) (hb : d324747 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269220, d324747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269220, d324747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104258 (p : Pattern) (ha : d269226 p = 1) (hb : d324753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269109 q = 1) (hb : d324679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269109, d324679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104233 q ha hb
    | true =>
      simp only [d269109, d324679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104234 q ha hb
  have h2 (q : Pattern) (ha : d269110 q = 1) (hb : d324680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269110, d324680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269110, d324680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269111 q = 1) (hb : d324681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269111, d324681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269111, d324681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269112 q = 1) (hb : d324682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269112, d324682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269112, d324682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269119 q = 1) (hb : d324689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269119, d324689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104235 q ha hb
    | true =>
      simp only [d269119, d324689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104236 q ha hb
  have h6 (q : Pattern) (ha : d269120 q = 1) (hb : d324690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269120, d324690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269120, d324690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269121 q = 1) (hb : d324691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269121, d324691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269121, d324691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269171 q = 1) (hb : d324705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269171, d324705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104242 q ha hb
    | true =>
      simp only [d269171, d324705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104243 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269086 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d269172 q = 1) (hb : d324706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269172, d324706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269172, d324706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d269199 q = 1) (hb : d324727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269199, d324727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104249 q ha hb
    | true =>
      simp only [d269199, d324727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269200 q = 1) (hb : d324728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269200, d324728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269200, d324728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269201 q = 1) (hb : d324729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269201, d324729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269201, d324729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269202 q = 1) (hb : d324730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269202, d324730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269202, d324730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269203 q = 1) (hb : d324731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269203, d324731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269203, d324731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269207 q = 1) (hb : d324735 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269207, d324735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104251 q ha hb
    | true =>
      simp only [d269207, d324735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104252 q ha hb
  have h17 (q : Pattern) (ha : d269208 q = 1) (hb : d324736 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269208, d324736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269208, d324736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269209 q = 1) (hb : d324737 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269209, d324737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269209, d324737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d269210 q = 1) (hb : d324738 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269210, d324738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269210, d324738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d269213 q = 1) (hb : d324741 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269213, d324741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104253 q ha hb
    | true =>
      simp only [d269213, d324741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104254 q ha hb
  have h21 (q : Pattern) (ha : d269214 q = 1) (hb : d324742 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269214, d324742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269214, d324742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d269215 q = 1) (hb : d324743 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269215, d324743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269215, d324743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d269218 q = 1) (hb : d324745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269218, d324745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104255 q ha hb
    | true =>
      simp only [d269218, d324745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104256 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d269096 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d269219 q = 1) (hb : d324746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269219, d324746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d269219, d324746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d269221 q = 1) (hb : d324748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269221, d324748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104257 q ha hb
    | true =>
      simp only [d269221, d324748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d269222 q = 1) (hb : d324749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269222, d324749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d269222, d324749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d269223 q = 1) (hb : d324750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269223, d324750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d269223, d324750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d269224 q = 1) (hb : d324751 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269224, d324751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d269224, d324751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d269225 q = 1) (hb : d324752 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269225, d324752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269225, d324752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d269226 q = 1) (hb : d324753 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269226, d324753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269226, d324753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro104259 (p : Pattern) (ha : d269238 p = 1) (hb : d324760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269228 q = 1) (hb : d324656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269228, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104243 q ha hb
    | true =>
      simp only [d269228, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104228 q ha hb
  have h2 (q : Pattern) (ha : d269229 q = 1) (hb : d324657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269229, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269229, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269230 q = 1) (hb : d324658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269230, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269230, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269231 q = 1) (hb : d324659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269231, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269231, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269232 q = 1) (hb : d324660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269232, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269232, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269233 q = 1) (hb : d324755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269233, d324755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104228 q ha hb
    | true =>
      simp only [d269233, d324755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269234 q = 1) (hb : d324756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269234, d324756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269234, d324756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269235 q = 1) (hb : d324757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269235, d324757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269235, d324757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269236 q = 1) (hb : d324758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269236, d324758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269236, d324758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269237 q = 1) (hb : d324759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269237, d324759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269237, d324759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269238 q = 1) (hb : d324760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269238, d324760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269238, d324760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104260 (p : Pattern) (ha : d269244 p = 1) (hb : d324766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269233 q = 1) (hb : d324755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269233, d324755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104228 q ha hb
    | true =>
      simp only [d269233, d324755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269234 q = 1) (hb : d324756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269234, d324756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269234, d324756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269235 q = 1) (hb : d324757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269235, d324757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269235, d324757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269236 q = 1) (hb : d324758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269236, d324758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269236, d324758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269237 q = 1) (hb : d324759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269237, d324759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269237, d324759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269239 q = 1) (hb : d324761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269239, d324761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104231 q ha hb
    | true =>
      simp only [d269239, d324761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269240 q = 1) (hb : d324762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269240, d324762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269240, d324762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269241 q = 1) (hb : d324763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269241, d324763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269241, d324763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269242 q = 1) (hb : d324764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269242, d324764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269242, d324764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269243 q = 1) (hb : d324765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269243, d324765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269243, d324765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269244 q = 1) (hb : d324766 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269244, d324766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269244, d324766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104261 (p : Pattern) (ha : d269251 p = 1) (hb : d324773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269218 q = 1) (hb : d324745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269218, d324745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104255 q ha hb
    | true =>
      simp only [d269218, d324745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104256 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269096 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269219 q = 1) (hb : d324746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269219, d324746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269219, d324746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d269221 q = 1) (hb : d324748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269221, d324748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104257 q ha hb
    | true =>
      simp only [d269221, d324748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269222 q = 1) (hb : d324749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269222, d324749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269222, d324749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269223 q = 1) (hb : d324750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269223, d324750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269223, d324750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269249 q = 1) (hb : d324771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269249, d324771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269249, d324771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269250 q = 1) (hb : d324772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269250, d324772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269250, d324772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269251 q = 1) (hb : d324773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269251, d324773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269251, d324773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro104262 (p : Pattern) (ha : d269253 p = 1) (hb : d324775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269239 q = 1) (hb : d324761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269239, d324761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104231 q ha hb
    | true =>
      simp only [d269239, d324761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269240 q = 1) (hb : d324762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269240, d324762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269240, d324762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269241 q = 1) (hb : d324763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269241, d324763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269241, d324763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269242 q = 1) (hb : d324764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269242, d324764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269242, d324764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269243 q = 1) (hb : d324765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269243, d324765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269243, d324765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269253 q = 1) (hb : d324775 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269253, d324775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269253, d324775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104263 (p : Pattern) (ha : d269273 p = 1) (hb : d324786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269267 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269268 q = 1) (hb : d324781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269268, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269268, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104215 q ha hb
  have h3 (q : Pattern) (ha : d268997 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d268997, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104215 q ha hb
    | true =>
      simp only [d268997, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d269269 q = 1) (hb : d324782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269269, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269269, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d268998 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d268998, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268998, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d269270 q = 1) (hb : d324783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269270, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269270, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269271 q = 1) (hb : d324784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269271, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269271, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d269272 q = 1) (hb : d324785 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269272, d324785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269272, d324785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269273 q = 1) (hb : d324786 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269273, d324786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269273, d324786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro104264 (p : Pattern) (ha : d269288 p = 1) (hb : d324792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269278 q = 1) (hb : d324781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269278, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269278, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104214 q ha hb
  have h3 (q : Pattern) (ha : d268988 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d268988, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104214 q ha hb
    | true =>
      simp only [d268988, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d269279 q = 1) (hb : d324782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269279, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269279, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d268989 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d268989, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268989, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d269280 q = 1) (hb : d324783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269280, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269280, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269281 q = 1) (hb : d324784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269281, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269281, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d269282 q = 1) (hb : d324785 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269282, d324785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269282, d324785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269268 q = 1) (hb : d324781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269268, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269268, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104215 q ha hb
  have h10 (q : Pattern) (ha : d268997 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d268997, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104215 q ha hb
    | true =>
      simp only [d268997, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d269269 q = 1) (hb : d324782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269269, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269269, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d268998 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d268998, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268998, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d269270 q = 1) (hb : d324783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269270, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269270, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269271 q = 1) (hb : d324784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269271, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269271, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d269283 q = 1) (hb : d324787 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269283, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269283, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104216 q ha hb
  have h16 (q : Pattern) (ha : d269013 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269013, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104216 q ha hb
    | true =>
      simp only [d269013, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h17 (q : Pattern) (ha : d269284 q = 1) (hb : d324788 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269284, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269284, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269014 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269014, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269014, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h19 (q : Pattern) (ha : d269285 q = 1) (hb : d324789 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269285, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269285, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d269286 q = 1) (hb : d324790 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269286, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269286, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h21 (q : Pattern) (ha : d269287 q = 1) (hb : d324791 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269287, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269287, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d269288 q = 1) (hb : d324792 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269288, d324792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269288, d324792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro104265 (p : Pattern) (ha : d269298 p = 1) (hb : d324797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269292 q = 1) (hb : d324781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269292, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269292, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104238 q ha hb
  have h2 (q : Pattern) (ha : d269144 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269144, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104238 q ha hb
    | true =>
      simp only [d269144, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269293 q = 1) (hb : d324782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269293, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269293, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269145 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269145, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269145, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269294 q = 1) (hb : d324783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269294, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269294, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269295 q = 1) (hb : d324784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269295, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269295, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269283 q = 1) (hb : d324787 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269283, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269283, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104216 q ha hb
  have h8 (q : Pattern) (ha : d269013 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269013, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104216 q ha hb
    | true =>
      simp only [d269013, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269284 q = 1) (hb : d324788 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269284, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269284, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269014 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269014, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269014, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269285 q = 1) (hb : d324789 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269285, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269285, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269286 q = 1) (hb : d324790 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269286, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269286, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269296 q = 1) (hb : d324791 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269296, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269296, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269297 q = 1) (hb : d324796 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269297, d324796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269297, d324796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269298 q = 1) (hb : d324797 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269298, d324797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269298, d324797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104266 (p : Pattern) (ha : d269312 p = 1) (hb : d324797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269303 q = 1) (hb : d324781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269303, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269303, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104218 q ha hb
  have h2 (q : Pattern) (ha : d269026 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269026, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104218 q ha hb
    | true =>
      simp only [d269026, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269304 q = 1) (hb : d324782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269304, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269304, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269027 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269027, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269027, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269305 q = 1) (hb : d324783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269305, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269305, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269306 q = 1) (hb : d324784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269306, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269306, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269307 q = 1) (hb : d324787 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269307, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269307, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104219 q ha hb
  have h8 (q : Pattern) (ha : d269031 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269031, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104219 q ha hb
    | true =>
      simp only [d269031, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269308 q = 1) (hb : d324788 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269308, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269308, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269032 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269032, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269032, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269309 q = 1) (hb : d324789 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269309, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269309, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269310 q = 1) (hb : d324790 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269310, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269310, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269311 q = 1) (hb : d324791 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269311, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269311, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269283 q = 1) (hb : d324787 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269283, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269283, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104216 q ha hb
  have h15 (q : Pattern) (ha : d269013 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269013, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104216 q ha hb
    | true =>
      simp only [d269013, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269284 q = 1) (hb : d324788 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269284, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269284, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269014 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269014, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269014, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d269285 q = 1) (hb : d324789 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269285, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269285, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269286 q = 1) (hb : d324790 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269286, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269286, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d269297 q = 1) (hb : d324796 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269297, d324796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269297, d324796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269312 q = 1) (hb : d324797 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269312, d324797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269312, d324797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro104267 (p : Pattern) (ha : d269326 p = 1) (hb : d324802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269316 q = 1) (hb : d324787 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269316, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269316, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104222 q ha hb
  have h2 (q : Pattern) (ha : d269045 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269045, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104222 q ha hb
    | true =>
      simp only [d269045, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269317 q = 1) (hb : d324788 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269317, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269317, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269046 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269046, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269046, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269318 q = 1) (hb : d324789 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269318, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269318, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269319 q = 1) (hb : d324790 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269319, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269319, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269320 q = 1) (hb : d324796 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269320, d324796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269320, d324796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d221342 q = 1) (hb : d269321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d221342, d269321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d221342, d269321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104221 q ha hb
  have h9 (q : Pattern) (ha : d221102 q = 1) (hb : d269054 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d221102, d269054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104221 q ha hb
    | true =>
      simp only [d221102, d269054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d221343 q = 1) (hb : d269322 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d221343, d269322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d221343, d269322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d221103 q = 1) (hb : d269055 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d221103, d269055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d221103, d269055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d221344 q = 1) (hb : d269323 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d221344, d269323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d221344, d269323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d221345 q = 1) (hb : d269324 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d221345, d269324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d221345, d269324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d221346 q = 1) (hb : d269325 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d221346, d269325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d221346, d269325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d269326 q = 1) (hb : d324802 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269326, d324802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269326, d324802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro104268 (p : Pattern) (ha : d269332 p = 1) (hb : d324808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269289 q = 1) (hb : d324793 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269289, d324793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104263 q ha hb
    | true =>
      simp only [d269289, d324793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104264 q ha hb
  have h2 (q : Pattern) (ha : d269290 q = 1) (hb : d324794 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269290, d324794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269290, d324794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269291 q = 1) (hb : d324795 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269291, d324795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269291, d324795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269299 q = 1) (hb : d324798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269299, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104264 q ha hb
    | true =>
      simp only [d269299, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104265 q ha hb
  have h5 (q : Pattern) (ha : d269300 q = 1) (hb : d324799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269300, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269300, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269301 q = 1) (hb : d324800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269301, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269301, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269302 q = 1) (hb : d324801 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269302, d324801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269302, d324801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269313 q = 1) (hb : d324798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269313, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104264 q ha hb
    | true =>
      simp only [d269313, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104266 q ha hb
  have h9 (q : Pattern) (ha : d269314 q = 1) (hb : d324799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269314, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269314, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269315 q = 1) (hb : d324800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269315, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269315, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269327 q = 1) (hb : d324803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269327, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104266 q ha hb
    | true =>
      simp only [d269327, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104267 q ha hb
  have h12 (q : Pattern) (ha : d269328 q = 1) (hb : d324804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269328, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269328, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269329 q = 1) (hb : d324805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269329, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269329, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269330 q = 1) (hb : d324806 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269330, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269330, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269331 q = 1) (hb : d324807 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269331, d324807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269331, d324807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269332 q = 1) (hb : d324808 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269332, d324808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269332, d324808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro104269 (p : Pattern) (ha : d269337 p = 1) (hb : d324813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269313 q = 1) (hb : d324798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269313, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104264 q ha hb
    | true =>
      simp only [d269313, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104266 q ha hb
  have h2 (q : Pattern) (ha : d269314 q = 1) (hb : d324799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269314, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269314, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269315 q = 1) (hb : d324800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269315, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269315, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269327 q = 1) (hb : d324803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269327, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104266 q ha hb
    | true =>
      simp only [d269327, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104267 q ha hb
  have h5 (q : Pattern) (ha : d269328 q = 1) (hb : d324804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269328, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269328, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269329 q = 1) (hb : d324805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269329, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269329, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269330 q = 1) (hb : d324806 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269330, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269330, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269335 q = 1) (hb : d324811 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269335, d324811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269335, d324811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269336 q = 1) (hb : d324812 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269336, d324812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269336, d324812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269337 q = 1) (hb : d324813 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269337, d324813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269337, d324813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro104270 (p : Pattern) (ha : d269343 p = 1) (hb : d324819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269333 q = 1) (hb : d324809 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269333, d324809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104268 q ha hb
    | true =>
      simp only [d269333, d324809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269334 q = 1) (hb : d324810 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269334, d324810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269334, d324810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269338 q = 1) (hb : d324814 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269338, d324814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104269 q ha hb
    | true =>
      simp only [d269338, d324814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269339 q = 1) (hb : d324815 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269339, d324815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269339, d324815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269340 q = 1) (hb : d324816 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269340, d324816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269340, d324816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269341 q = 1) (hb : d324817 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269341, d324817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269341, d324817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269342 q = 1) (hb : d324818 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269342, d324818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269342, d324818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269343 q = 1) (hb : d324819 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269343, d324819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269343, d324819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104271 (p : Pattern) (ha : d269345 p = 1) (hb : d324802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269307 q = 1) (hb : d324787 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269307, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269307, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104219 q ha hb
  have h2 (q : Pattern) (ha : d269031 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269031, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104219 q ha hb
    | true =>
      simp only [d269031, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269308 q = 1) (hb : d324788 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269308, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269308, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269032 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269032, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269032, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269309 q = 1) (hb : d324789 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269309, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269309, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269310 q = 1) (hb : d324790 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269310, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269310, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269344 q = 1) (hb : d324796 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269344, d324796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269344, d324796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d221342 q = 1) (hb : d269321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d221342, d269321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d221342, d269321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104221 q ha hb
  have h9 (q : Pattern) (ha : d221102 q = 1) (hb : d269054 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d221102, d269054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104221 q ha hb
    | true =>
      simp only [d221102, d269054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d221343 q = 1) (hb : d269322 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d221343, d269322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d221343, d269322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d221103 q = 1) (hb : d269055 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d221103, d269055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d221103, d269055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d221344 q = 1) (hb : d269323 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d221344, d269323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d221344, d269323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d221345 q = 1) (hb : d269324 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d221345, d269324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d221345, d269324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d221346 q = 1) (hb : d269325 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d221346, d269325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d221346, d269325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d269345 q = 1) (hb : d324802 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269345, d324802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269345, d324802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro104272 (p : Pattern) (ha : d269351 p = 1) (hb : d324821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269346 q = 1) (hb : d324803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269346, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104266 q ha hb
    | true =>
      simp only [d269346, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104271 q ha hb
  have h2 (q : Pattern) (ha : d269347 q = 1) (hb : d324804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269347, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269347, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269348 q = 1) (hb : d324805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269348, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269348, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269349 q = 1) (hb : d324811 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269349, d324811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269349, d324811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269350 q = 1) (hb : d324820 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269350, d324820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269350, d324820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269351 q = 1) (hb : d324821 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269351, d324821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269351, d324821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104273 (p : Pattern) (ha : d269357 p = 1) (hb : d324827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269338 q = 1) (hb : d324814 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269338, d324814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104269 q ha hb
    | true =>
      simp only [d269338, d324814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269339 q = 1) (hb : d324815 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269339, d324815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269339, d324815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269352 q = 1) (hb : d324822 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269352, d324822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104272 q ha hb
    | true =>
      simp only [d269352, d324822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269353 q = 1) (hb : d324823 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269353, d324823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269353, d324823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269354 q = 1) (hb : d324824 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269354, d324824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269354, d324824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269355 q = 1) (hb : d324825 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269355, d324825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269355, d324825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269356 q = 1) (hb : d324826 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269356, d324826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269356, d324826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269357 q = 1) (hb : d324827 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269357, d324827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269357, d324827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104274 (p : Pattern) (ha : d269378 p = 1) (hb : d324835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269303 q = 1) (hb : d324781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269303, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269303, d324781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104218 q ha hb
  have h2 (q : Pattern) (ha : d269026 q = 1) (hb : d324617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269026, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104218 q ha hb
    | true =>
      simp only [d269026, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269304 q = 1) (hb : d324782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269304, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269304, d324782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269027 q = 1) (hb : d324618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269027, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269027, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269305 q = 1) (hb : d324783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269305, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269305, d324783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269306 q = 1) (hb : d324784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269306, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269306, d324784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269307 q = 1) (hb : d324787 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269307, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269307, d324787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104219 q ha hb
  have h8 (q : Pattern) (ha : d269031 q = 1) (hb : d324623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269031, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104219 q ha hb
    | true =>
      simp only [d269031, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269308 q = 1) (hb : d324788 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269308, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269308, d324788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269032 q = 1) (hb : d324624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269032, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269032, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269309 q = 1) (hb : d324789 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269309, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269309, d324789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269310 q = 1) (hb : d324790 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269310, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269310, d324790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269311 q = 1) (hb : d324791 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269311, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269311, d324791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269373 q = 1) (hb : d324830 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269373, d324830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269373, d324830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104244 q ha hb
  have h15 (q : Pattern) (ha : d269174 q = 1) (hb : d324708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269174, d324708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104244 q ha hb
    | true =>
      simp only [d269174, d324708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269374 q = 1) (hb : d324831 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269374, d324831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269374, d324831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269175 q = 1) (hb : d324709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269175, d324709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269175, d324709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d269375 q = 1) (hb : d324832 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269375, d324832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269375, d324832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269376 q = 1) (hb : d324833 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269376, d324833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269376, d324833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d269377 q = 1) (hb : d324834 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269377, d324834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269377, d324834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269378 q = 1) (hb : d324835 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269378, d324835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269378, d324835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro104275 (p : Pattern) (ha : d269384 p = 1) (hb : d324836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269379 q = 1) (hb : d324830 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269379, d324830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269379, d324830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104246 q ha hb
  have h2 (q : Pattern) (ha : d269181 q = 1) (hb : d324708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269181, d324708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104246 q ha hb
    | true =>
      simp only [d269181, d324708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269380 q = 1) (hb : d324831 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269380, d324831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269380, d324831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269182 q = 1) (hb : d324709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269182, d324709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269182, d324709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269381 q = 1) (hb : d324832 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269381, d324832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269381, d324832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269382 q = 1) (hb : d324833 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269382, d324833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269382, d324833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269383 q = 1) (hb : d324834 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269383, d324834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269383, d324834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269384 q = 1) (hb : d324836 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269384, d324836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269384, d324836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104276 (p : Pattern) (ha : d269390 p = 1) (hb : d324842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269313 q = 1) (hb : d324798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269313, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104264 q ha hb
    | true =>
      simp only [d269313, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104266 q ha hb
  have h2 (q : Pattern) (ha : d269314 q = 1) (hb : d324799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269314, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269314, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269315 q = 1) (hb : d324800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269315, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269315, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269327 q = 1) (hb : d324803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269327, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104266 q ha hb
    | true =>
      simp only [d269327, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104267 q ha hb
  have h5 (q : Pattern) (ha : d269328 q = 1) (hb : d324804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269328, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269328, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269329 q = 1) (hb : d324805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269329, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269329, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269330 q = 1) (hb : d324806 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269330, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269330, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269385 q = 1) (hb : d324837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269385, d324837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104274 q ha hb
    | true =>
      simp only [d269385, d324837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104275 q ha hb
  have h9 (q : Pattern) (ha : d269386 q = 1) (hb : d324838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269386, d324838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269386, d324838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269387 q = 1) (hb : d324839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269387, d324839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269387, d324839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269388 q = 1) (hb : d324840 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269388, d324840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269388, d324840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269389 q = 1) (hb : d324841 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269389, d324841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269389, d324841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269390 q = 1) (hb : d324842 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269390, d324842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269390, d324842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro104277 (p : Pattern) (ha : d269396 p = 1) (hb : d324848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269391 q = 1) (hb : d324843 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269391, d324843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104276 q ha hb
    | true =>
      simp only [d269391, d324843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269392 q = 1) (hb : d324844 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269392, d324844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269392, d324844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269393 q = 1) (hb : d324845 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269393, d324845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269393, d324845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269394 q = 1) (hb : d324846 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269394, d324846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269394, d324846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269395 q = 1) (hb : d324847 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269395, d324847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269395, d324847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269396 q = 1) (hb : d324848 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269396, d324848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269396, d324848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104278 (p : Pattern) (ha : d269402 p = 1) (hb : d324854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269358 q = 1) (hb : d324828 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269358, d324828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104270 q ha hb
    | true =>
      simp only [d269358, d324828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104273 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269371 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269372 q = 1) (hb : d324829 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269372, d324829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269372, d324829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d269397 q = 1) (hb : d324849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269397, d324849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104277 q ha hb
    | true =>
      simp only [d269397, d324849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269398 q = 1) (hb : d324850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269398, d324850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269398, d324850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269399 q = 1) (hb : d324851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269399, d324851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269399, d324851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269400 q = 1) (hb : d324852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269400, d324852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269400, d324852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269401 q = 1) (hb : d324853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269401, d324853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269401, d324853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269402 q = 1) (hb : d324854 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269402, d324854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269402, d324854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro104279 (p : Pattern) (ha : d269370 p = 1) (hb : d324859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269352 q = 1) (hb : d324822 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269352, d324822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104272 q ha hb
    | true =>
      simp only [d269352, d324822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269353 q = 1) (hb : d324823 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269353, d324823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269353, d324823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269367 q = 1) (hb : d324856 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269367, d324856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269367, d324856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269368 q = 1) (hb : d324857 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269368, d324857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269368, d324857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269369 q = 1) (hb : d324858 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269369, d324858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269369, d324858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269370 q = 1) (hb : d324859 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269370, d324859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269370, d324859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104280 (p : Pattern) (ha : d269409 p = 1) (hb : d324865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269404 q = 1) (hb : d324860 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269404, d324860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104279 q ha hb
    | true =>
      simp only [d269404, d324860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269405 q = 1) (hb : d324861 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269405, d324861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269405, d324861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269406 q = 1) (hb : d324862 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269406, d324862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269406, d324862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269407 q = 1) (hb : d324863 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269407, d324863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269407, d324863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269408 q = 1) (hb : d324864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269408, d324864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269408, d324864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269409 q = 1) (hb : d324865 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269409, d324865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269409, d324865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104281 (p : Pattern) (ha : d269415 p = 1) (hb : d324871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269092 q = 1) (hb : d324662 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269092, d324662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269092, d324662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104229 q ha hb
  have h2 (q : Pattern) (ha : d269093 q = 1) (hb : d324663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269093, d324663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269093, d324663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269102 q = 1) (hb : d324672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269102, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104229 q ha hb
    | true =>
      simp only [d269102, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104232 q ha hb
  have h4 (q : Pattern) (ha : d269103 q = 1) (hb : d324673 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269103, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269103, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269104 q = 1) (hb : d324674 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269104, d324674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269104, d324674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269227 q = 1) (hb : d324754 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269227, d324754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104250 q ha hb
    | true =>
      simp only [d269227, d324754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104258 q ha hb
  have h7 (q : Pattern) (ha : d269245 q = 1) (hb : d324767 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269245, d324767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104259 q ha hb
    | true =>
      simp only [d269245, d324767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104260 q ha hb
  have h8 (q : Pattern) (ha : d269246 q = 1) (hb : d324768 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269246, d324768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269246, d324768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269247 q = 1) (hb : d324769 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269247, d324769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269247, d324769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269248 q = 1) (hb : d324770 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269248, d324770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269248, d324770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269252 q = 1) (hb : d324774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269252, d324774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269252, d324774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104261 q ha hb
  have h12 (q : Pattern) (ha : d269254 q = 1) (hb : d324776 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269254, d324776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269254, d324776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104262 q ha hb
  have h13 (q : Pattern) (ha : d269255 q = 1) (hb : d324777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269255, d324777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269255, d324777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269256 q = 1) (hb : d324778 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269256, d324778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269256, d324778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269257 q = 1) (hb : d324779 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269257, d324779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269257, d324779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269258 q = 1) (hb : d324780 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269258, d324780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269258, d324780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269403 q = 1) (hb : d324855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269403, d324855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269403, d324855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104278 q ha hb
  have h18 (q : Pattern) (ha : d269410 q = 1) (hb : d324866 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269410, d324866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269410, d324866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104280 q ha hb
  have h19 (q : Pattern) (ha : d269411 q = 1) (hb : d324867 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269411, d324867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269411, d324867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d269412 q = 1) (hb : d324868 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269412, d324868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269412, d324868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269413 q = 1) (hb : d324869 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269413, d324869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d269413, d324869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d269414 q = 1) (hb : d324870 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269414, d324870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269414, d324870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d269415 q = 1) (hb : d324871 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269415, d324871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269415, d324871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro104282 (p : Pattern) (ha : d269421 p = 1) (hb : d324877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269416 q = 1) (hb : d324872 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269416, d324872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269416, d324872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104281 q ha hb
  have h2 (q : Pattern) (ha : d269417 q = 1) (hb : d324873 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269417, d324873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269417, d324873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269418 q = 1) (hb : d324874 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269418, d324874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269418, d324874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269419 q = 1) (hb : d324875 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269419, d324875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269419, d324875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269420 q = 1) (hb : d324876 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269420, d324876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269420, d324876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269421 q = 1) (hb : d324877 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269421, d324877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269421, d324877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104283 (p : Pattern) (ha : d46867 p = 1) (hb : d53321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d44880 q = 1) (hb : d51979 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44880, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d53295 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, d53295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46864, d53295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d46865 q = 1) (hb : d53300 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, d53300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46865, d53300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d46866 q = 1) (hb : d53301 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46866, d53301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46866, d53301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d46867 q = 1) (hb : d53321 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46867, d53321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46867, d53321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro104284 (p : Pattern) (ha : d46876 p = 1) (hb : d269463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269456 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46868 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46868, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104283 q ha hb
  have h4 (q : Pattern) (ha : d46869 q = 1) (hb : d269457 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46869, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46869, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46870 q = 1) (hb : d269458 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46870, d269458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46870, d269458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d46871 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104283 q ha hb
    | true =>
      simp only [d46871, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d46872 q = 1) (hb : d269459 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46872, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46873 q = 1) (hb : d269460 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46873, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d46874 q = 1) (hb : d269461 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46874, d269461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46874, d269461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46875 q = 1) (hb : d269462 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46875, d269462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46875, d269462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d46876 q = 1) (hb : d269463 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46876, d269463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46876, d269463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro104285 (p : Pattern) (ha : d46882 p = 1) (hb : d269469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269447 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46877 q = 1) (hb : d269464 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104284 q ha hb
    | true =>
      simp only [d46877, d269464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46878 q = 1) (hb : d269465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46878, d269465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d46879 q = 1) (hb : d269466 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, d269466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46879, d269466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46880 q = 1) (hb : d269467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, d269467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46880, d269467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d46881 q = 1) (hb : d269468 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, d269468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46881, d269468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46882 q = 1) (hb : d269469 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46882, d269469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46882, d269469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104286 (p : Pattern) (ha : d46876 p = 1) (hb : d269481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269475 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46868 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46868, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104283 q ha hb
  have h4 (q : Pattern) (ha : d46869 q = 1) (hb : d269457 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46869, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46869, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46870 q = 1) (hb : d269458 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46870, d269458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46870, d269458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d46871 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104283 q ha hb
    | true =>
      simp only [d46871, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d46872 q = 1) (hb : d269459 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46872, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46873 q = 1) (hb : d269460 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46873, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d46874 q = 1) (hb : d269461 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46874, d269461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46874, d269461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46875 q = 1) (hb : d269462 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46875, d269462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46875, d269462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d46876 q = 1) (hb : d269481 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46876, d269481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46876, d269481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro104287 (p : Pattern) (ha : d46884 p = 1) (hb : d269488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269480 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d269482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104286 q ha hb
    | true =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46878 q = 1) (hb : d269483 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d46879 q = 1) (hb : d269484 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, d269484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46879, d269484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46880 q = 1) (hb : d269485 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, d269485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46880, d269485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d46881 q = 1) (hb : d269486 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, d269486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46881, d269486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46877 q = 1) (hb : d269464 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104284 q ha hb
    | true =>
      simp only [d46877, d269464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d46878 q = 1) (hb : d269465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46878, d269465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d46879 q = 1) (hb : d269466 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, d269466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46879, d269466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46880 q = 1) (hb : d269467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, d269467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46880, d269467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d46883 q = 1) (hb : d269487 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46883, d269487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46883, d269487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d46884 q = 1) (hb : d269488 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46884, d269488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46884, d269488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro104288 (p : Pattern) (ha : d46876 p = 1) (hb : d269495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269494 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46868 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46868, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104283 q ha hb
  have h4 (q : Pattern) (ha : d46869 q = 1) (hb : d269457 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46869, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46869, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46870 q = 1) (hb : d269458 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46870, d269458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46870, d269458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d46871 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104283 q ha hb
    | true =>
      simp only [d46871, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d46872 q = 1) (hb : d269459 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46872, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46873 q = 1) (hb : d269460 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46873, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d46874 q = 1) (hb : d269461 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46874, d269461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46874, d269461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46875 q = 1) (hb : d269462 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46875, d269462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46875, d269462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d46876 q = 1) (hb : d269495 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46876, d269495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46876, d269495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro104289 (p : Pattern) (ha : d46888 p = 1) (hb : d269504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46868 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46868, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104283 q ha hb
  have h3 (q : Pattern) (ha : d46869 q = 1) (hb : d269457 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46869, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46869, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46870 q = 1) (hb : d269501 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46870, d269501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46870, d269501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46871 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104283 q ha hb
    | true =>
      simp only [d46871, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d46872 q = 1) (hb : d269459 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46872, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46873 q = 1) (hb : d269460 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46873, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d46874 q = 1) (hb : d269502 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46874, d269502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46874, d269502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46875 q = 1) (hb : d269503 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46875, d269503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46875, d269503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d46888 q = 1) (hb : d269504 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46888, d269504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46888, d269504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h11 p ha hb
theorem andIntro104290 (p : Pattern) (ha : d46894 p = 1) (hb : d269510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46877 q = 1) (hb : d269496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104288 q ha hb
    | true =>
      simp only [d46877, d269496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46878 q = 1) (hb : d269497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46878, d269497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46879 q = 1) (hb : d269498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, d269498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46879, d269498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46880 q = 1) (hb : d269499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, d269499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46880, d269499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46883 q = 1) (hb : d269500 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46883, d269500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46883, d269500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46889 q = 1) (hb : d269505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, d269505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104289 q ha hb
    | true =>
      simp only [d46889, d269505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46890 q = 1) (hb : d269506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, d269506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46890, d269506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46891 q = 1) (hb : d269507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46891, d269507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46891, d269507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46892 q = 1) (hb : d269508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46892, d269508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46892, d269508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d46893 q = 1) (hb : d269509 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46893, d269509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46893, d269509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46894 q = 1) (hb : d269510 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46894, d269510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46894, d269510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104291 (p : Pattern) (ha : d46894 p = 1) (hb : d269516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46877 q = 1) (hb : d269482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104286 q ha hb
    | true =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46878 q = 1) (hb : d269483 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46879 q = 1) (hb : d269484 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, d269484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46879, d269484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46880 q = 1) (hb : d269485 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, d269485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46880, d269485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46883 q = 1) (hb : d269515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46883, d269515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46883, d269515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46889 q = 1) (hb : d269505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, d269505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104289 q ha hb
    | true =>
      simp only [d46889, d269505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46890 q = 1) (hb : d269506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, d269506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46890, d269506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46891 q = 1) (hb : d269507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46891, d269507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46891, d269507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46892 q = 1) (hb : d269508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46892, d269508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46892, d269508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d46893 q = 1) (hb : d269509 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46893, d269509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46893, d269509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46894 q = 1) (hb : d269516 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46894, d269516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46894, d269516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104292 (p : Pattern) (ha : d46901 p = 1) (hb : d269522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46885 q = 1) (hb : d269489 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, d269489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104285 q ha hb
    | true =>
      simp only [d46885, d269489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104287 q ha hb
  have h2 (q : Pattern) (ha : d46886 q = 1) (hb : d269490 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, d269490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46886, d269490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46887 q = 1) (hb : d269491 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, d269491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46887, d269491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46895 q = 1) (hb : d269511 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, d269511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104287 q ha hb
    | true =>
      simp only [d46895, d269511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104290 q ha hb
  have h5 (q : Pattern) (ha : d46896 q = 1) (hb : d269512 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, d269512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46896, d269512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46897 q = 1) (hb : d269513 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, d269513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46897, d269513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46898 q = 1) (hb : d269514 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, d269514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46898, d269514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46895 q = 1) (hb : d269517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, d269517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104287 q ha hb
    | true =>
      simp only [d46895, d269517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104291 q ha hb
  have h9 (q : Pattern) (ha : d46896 q = 1) (hb : d269518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, d269518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46896, d269518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46897 q = 1) (hb : d269519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, d269519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46897, d269519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46899 q = 1) (hb : d269520 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46899, d269520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46899, d269520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46900 q = 1) (hb : d269521 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46900, d269521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46900, d269521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46901 q = 1) (hb : d269522 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46901, d269522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46901, d269522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro104293 (p : Pattern) (ha : d46905 p = 1) (hb : d269526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46895 q = 1) (hb : d269517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, d269517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104287 q ha hb
    | true =>
      simp only [d46895, d269517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104291 q ha hb
  have h2 (q : Pattern) (ha : d46896 q = 1) (hb : d269518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, d269518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46896, d269518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46897 q = 1) (hb : d269519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, d269519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46897, d269519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46899 q = 1) (hb : d269520 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46899, d269520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46899, d269520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46904 q = 1) (hb : d269525 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46904, d269525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46904, d269525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46905 q = 1) (hb : d269526 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46905, d269526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46905, d269526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104294 (p : Pattern) (ha : d46911 p = 1) (hb : d269532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46902 q = 1) (hb : d269523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d269523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104292 q ha hb
    | true =>
      simp only [d46902, d269523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46903 q = 1) (hb : d269524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d269524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d269524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46908 q = 1) (hb : d269529 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d269529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, d269529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46909 q = 1) (hb : d269530 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, d269530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, d269530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46910 q = 1) (hb : d269531 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46910, d269531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46910, d269531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46911 q = 1) (hb : d269532 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46911, d269532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46911, d269532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104295 (p : Pattern) (ha : d46915 p = 1) (hb : d269536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46912 q = 1) (hb : d269533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d269533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, d269533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46913 q = 1) (hb : d269534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, d269534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, d269534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46914 q = 1) (hb : d269535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46914, d269535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46914, d269535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46915 q = 1) (hb : d269536 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46915, d269536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46915, d269536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104296 (p : Pattern) (ha : d46921 p = 1) (hb : d269542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46916 q = 1) (hb : d269537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, d269537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104294 q ha hb
    | true =>
      simp only [d46916, d269537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104295 q ha hb
  have h2 (q : Pattern) (ha : d46917 q = 1) (hb : d269538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d269538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46917, d269538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46918 q = 1) (hb : d269539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d269539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46918, d269539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46919 q = 1) (hb : d269540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d269540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46919, d269540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46920 q = 1) (hb : d269541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d269541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46920, d269541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46921 q = 1) (hb : d269542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46921, d269542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46921, d269542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104297 (p : Pattern) (ha : d46924 p = 1) (hb : d269545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46902 q = 1) (hb : d269523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d269523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104292 q ha hb
    | true =>
      simp only [d46902, d269523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46903 q = 1) (hb : d269524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d269524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d269524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46908 q = 1) (hb : d269529 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d269529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, d269529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46909 q = 1) (hb : d269530 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, d269530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, d269530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46910 q = 1) (hb : d269531 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46910, d269531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46910, d269531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46924 q = 1) (hb : d269545 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46924, d269545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46924, d269545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104298 (p : Pattern) (ha : d46925 p = 1) (hb : d269546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46912 q = 1) (hb : d269533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d269533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, d269533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46913 q = 1) (hb : d269534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, d269534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, d269534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46914 q = 1) (hb : d269535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46914, d269535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46914, d269535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46925 q = 1) (hb : d269546 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46925, d269546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46925, d269546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104299 (p : Pattern) (ha : d46931 p = 1) (hb : d269552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46916 q = 1) (hb : d269537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, d269537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104294 q ha hb
    | true =>
      simp only [d46916, d269537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104295 q ha hb
  have h2 (q : Pattern) (ha : d46917 q = 1) (hb : d269538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d269538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46917, d269538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46918 q = 1) (hb : d269539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d269539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46918, d269539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46919 q = 1) (hb : d269540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d269540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46919, d269540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46920 q = 1) (hb : d269541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d269541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46920, d269541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46926 q = 1) (hb : d269547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, d269547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104297 q ha hb
    | true =>
      simp only [d46926, d269547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104298 q ha hb
  have h7 (q : Pattern) (ha : d46927 q = 1) (hb : d269548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d269548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46927, d269548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46928 q = 1) (hb : d269549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d269549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46928, d269549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46929 q = 1) (hb : d269550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d269550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46929, d269550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46930 q = 1) (hb : d269551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d269551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46930, d269551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46931 q = 1) (hb : d269552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46931, d269552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46931, d269552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104300 (p : Pattern) (ha : d46901 p = 1) (hb : d269589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46885 q = 1) (hb : d269489 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, d269489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104285 q ha hb
    | true =>
      simp only [d46885, d269489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104287 q ha hb
  have h2 (q : Pattern) (ha : d46886 q = 1) (hb : d269490 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, d269490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46886, d269490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46887 q = 1) (hb : d269491 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, d269491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46887, d269491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46895 q = 1) (hb : d269511 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, d269511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104287 q ha hb
    | true =>
      simp only [d46895, d269511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104290 q ha hb
  have h5 (q : Pattern) (ha : d46896 q = 1) (hb : d269512 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, d269512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46896, d269512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46897 q = 1) (hb : d269513 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, d269513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46897, d269513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46898 q = 1) (hb : d269514 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, d269514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46898, d269514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46899 q = 1) (hb : d269587 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46899, d269587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46899, d269587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46900 q = 1) (hb : d269588 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46900, d269588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46900, d269588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46901 q = 1) (hb : d269589 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46901, d269589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46901, d269589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro104301 (p : Pattern) (ha : d46911 p = 1) (hb : d269599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46902 q = 1) (hb : d269590 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d269590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104300 q ha hb
    | true =>
      simp only [d46902, d269590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46903 q = 1) (hb : d269591 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d269591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d269591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46908 q = 1) (hb : d269596 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d269596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, d269596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46909 q = 1) (hb : d269597 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, d269597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, d269597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46910 q = 1) (hb : d269598 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46910, d269598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46910, d269598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46911 q = 1) (hb : d269599 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46911, d269599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46911, d269599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104302 (p : Pattern) (ha : d47065 p = 1) (hb : d269667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46916 q = 1) (hb : d269657 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, d269657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104301 q ha hb
    | true =>
      simp only [d46916, d269657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104295 q ha hb
  have h2 (q : Pattern) (ha : d46917 q = 1) (hb : d269658 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d269658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46917, d269658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46918 q = 1) (hb : d269659 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d269659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46918, d269659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46919 q = 1) (hb : d269660 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d269660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46919, d269660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46920 q = 1) (hb : d269661 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d269661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46920, d269661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47060 q = 1) (hb : d269662 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47060, d269662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104295 q ha hb
    | true =>
      simp only [d47060, d269662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47061 q = 1) (hb : d269663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47061, d269663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47061, d269663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47062 q = 1) (hb : d269664 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47062, d269664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47062, d269664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d47063 q = 1) (hb : d269665 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47063, d269665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47063, d269665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d47064 q = 1) (hb : d269666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47064, d269666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47064, d269666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d47065 q = 1) (hb : d269667 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47065, d269667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47065, d269667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104303 (p : Pattern) (ha : d47071 p = 1) (hb : d269673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47060 q = 1) (hb : d269662 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47060, d269662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104295 q ha hb
    | true =>
      simp only [d47060, d269662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47061 q = 1) (hb : d269663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47061, d269663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47061, d269663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47062 q = 1) (hb : d269664 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47062, d269664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47062, d269664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47063 q = 1) (hb : d269665 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47063, d269665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47063, d269665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47064 q = 1) (hb : d269666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47064, d269666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47064, d269666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47066 q = 1) (hb : d269668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47066, d269668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104298 q ha hb
    | true =>
      simp only [d47066, d269668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47067 q = 1) (hb : d269669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47067, d269669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47067, d269669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47068 q = 1) (hb : d269670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47068, d269670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47068, d269670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d47069 q = 1) (hb : d269671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47069, d269671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47069, d269671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d47070 q = 1) (hb : d269672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47070, d269672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47070, d269672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d47071 q = 1) (hb : d269673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47071, d269673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47071, d269673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104304 (p : Pattern) (ha : d47080 p = 1) (hb : d269682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47066 q = 1) (hb : d269668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47066, d269668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104298 q ha hb
    | true =>
      simp only [d47066, d269668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47067 q = 1) (hb : d269669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47067, d269669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47067, d269669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47068 q = 1) (hb : d269670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47068, d269670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47068, d269670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47069 q = 1) (hb : d269671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47069, d269671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47069, d269671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47070 q = 1) (hb : d269672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47070, d269672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47070, d269672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47080 q = 1) (hb : d269682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47080, d269682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47080, d269682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104305 (p : Pattern) (ha : d47096 p = 1) (hb : d269727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d47086 q = 1) (hb : d269722 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d269722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47086, d269722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104286 q ha hb
  have h3 (q : Pattern) (ha : d46877 q = 1) (hb : d269482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104286 q ha hb
    | true =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d47087 q = 1) (hb : d269723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d269723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47087, d269723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46878 q = 1) (hb : d269483 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d47088 q = 1) (hb : d269724 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d269724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47088, d269724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47089 q = 1) (hb : d269725 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d269725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47089, d269725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d47090 q = 1) (hb : d269726 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, d269726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47090, d269726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d47086 q = 1) (hb : d269703 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d269703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47086, d269703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104284 q ha hb
  have h10 (q : Pattern) (ha : d46877 q = 1) (hb : d269464 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104284 q ha hb
    | true =>
      simp only [d46877, d269464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d47087 q = 1) (hb : d269704 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d269704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d47087, d269704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46878 q = 1) (hb : d269465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46878, d269465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d47088 q = 1) (hb : d269705 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d269705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d47088, d269705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d47089 q = 1) (hb : d269706 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d269706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d47089, d269706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d47095 q = 1) (hb : d269712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, d269712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d47095, d269712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d47096 q = 1) (hb : d269727 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47096, d269727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47096, d269727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro104306 (p : Pattern) (ha : d47106 p = 1) (hb : d269760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47086 q = 1) (hb : d269722 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d269722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47086, d269722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104286 q ha hb
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d269482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104286 q ha hb
    | true =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47087 q = 1) (hb : d269723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d269723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, d269723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46878 q = 1) (hb : d269483 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47088 q = 1) (hb : d269724 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d269724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, d269724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47089 q = 1) (hb : d269725 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d269725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, d269725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47095 q = 1) (hb : d269759 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, d269759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, d269759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47101 q = 1) (hb : d269736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, d269736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47101, d269736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104289 q ha hb
  have h9 (q : Pattern) (ha : d46889 q = 1) (hb : d269505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, d269505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104289 q ha hb
    | true =>
      simp only [d46889, d269505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d47102 q = 1) (hb : d269737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, d269737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47102, d269737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46890 q = 1) (hb : d269506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, d269506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46890, d269506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d47103 q = 1) (hb : d269738 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47103, d269738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d47103, d269738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d47104 q = 1) (hb : d269739 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47104, d269739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d47104, d269739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d47105 q = 1) (hb : d269740 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47105, d269740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d47105, d269740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d47106 q = 1) (hb : d269760 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47106, d269760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47106, d269760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104307 (p : Pattern) (ha : d47125 p = 1) (hb : d269766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47107 q = 1) (hb : d269761 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d269761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104305 q ha hb
    | true =>
      simp only [d47107, d269761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104306 q ha hb
  have h2 (q : Pattern) (ha : d47108 q = 1) (hb : d269762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d269762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47108, d269762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47109 q = 1) (hb : d269763 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d269763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47109, d269763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d47115 q = 1) (hb : d269764 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47115, d269764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47115, d269764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47124 q = 1) (hb : d269765 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47124, d269765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47124, d269765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47125 q = 1) (hb : d269766 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47125, d269766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47125, d269766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104308 (p : Pattern) (ha : d47216 p = 1) (hb : d269844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47126 q = 1) (hb : d269767 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47126, d269767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104307 q ha hb
    | true =>
      simp only [d47126, d269767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47127 q = 1) (hb : d269768 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47127, d269768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47127, d269768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47213 q = 1) (hb : d269841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47213, d269841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47213, d269841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47214 q = 1) (hb : d269842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47214, d269842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47214, d269842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47215 q = 1) (hb : d269843 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47215, d269843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47215, d269843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47216 q = 1) (hb : d269844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47216, d269844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47216, d269844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104309 (p : Pattern) (ha : d47222 p = 1) (hb : d269850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47217 q = 1) (hb : d269845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47217, d269845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104308 q ha hb
    | true =>
      simp only [d47217, d269845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47218 q = 1) (hb : d269846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47218, d269846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47218, d269846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47219 q = 1) (hb : d269847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47219, d269847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47219, d269847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47220 q = 1) (hb : d269848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47220, d269848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47220, d269848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47221 q = 1) (hb : d269849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47221, d269849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47221, d269849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47222 q = 1) (hb : d269850 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47222, d269850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47222, d269850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104310 (p : Pattern) (ha : d46936 p = 1) (hb : d269557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46902 q = 1) (hb : d269523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d269523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104292 q ha hb
    | true =>
      simp only [d46902, d269523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46903 q = 1) (hb : d269524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d269524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d269524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46908 q = 1) (hb : d269529 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d269529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, d269529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46909 q = 1) (hb : d269530 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, d269530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, d269530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46935 q = 1) (hb : d269556 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46935, d269556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46935, d269556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46936 q = 1) (hb : d269557 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46936, d269557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46936, d269557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104311 (p : Pattern) (ha : d46938 p = 1) (hb : d269559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46912 q = 1) (hb : d269533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d269533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, d269533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46913 q = 1) (hb : d269534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, d269534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, d269534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46937 q = 1) (hb : d269558 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46937, d269558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46937, d269558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46938 q = 1) (hb : d269559 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46938, d269559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46938, d269559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104312 (p : Pattern) (ha : d46945 p = 1) (hb : d269566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46902 q = 1) (hb : d269523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d269523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104292 q ha hb
    | true =>
      simp only [d46902, d269523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46903 q = 1) (hb : d269524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d269524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d269524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46908 q = 1) (hb : d269529 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d269529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, d269529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46943 q = 1) (hb : d269564 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46943, d269564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46943, d269564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46944 q = 1) (hb : d269565 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46944, d269565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46944, d269565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46945 q = 1) (hb : d269566 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46945, d269566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46945, d269566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104313 (p : Pattern) (ha : d46948 p = 1) (hb : d269569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46912 q = 1) (hb : d269533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d269533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, d269533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46946 q = 1) (hb : d269567 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46946, d269567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46946, d269567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46947 q = 1) (hb : d269568 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46947, d269568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46947, d269568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46948 q = 1) (hb : d269569 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46948, d269569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46948, d269569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104314 (p : Pattern) (ha : d46884 p = 1) (hb : d269578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269452 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d269464 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104284 q ha hb
    | true =>
      simp only [d46877, d269464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46878 q = 1) (hb : d269465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d269465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d46879 q = 1) (hb : d269466 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, d269466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46879, d269466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46880 q = 1) (hb : d269467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, d269467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46880, d269467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d46881 q = 1) (hb : d269468 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, d269468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46881, d269468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46883 q = 1) (hb : d269487 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46883, d269487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46883, d269487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d46884 q = 1) (hb : d269578 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46884, d269578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46884, d269578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104315 (p : Pattern) (ha : d46957 p = 1) (hb : d269584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46952 q = 1) (hb : d269575 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46952, d269575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46952, d269575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104285 q ha hb
  have h3 (q : Pattern) (ha : d46953 q = 1) (hb : d269576 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46953, d269576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46953, d269576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46954 q = 1) (hb : d269577 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46954, d269577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46954, d269577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46885 q = 1) (hb : d269579 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, d269579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104285 q ha hb
    | true =>
      simp only [d46885, d269579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104314 q ha hb
  have h6 (q : Pattern) (ha : d46886 q = 1) (hb : d269580 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, d269580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46886, d269580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46887 q = 1) (hb : d269581 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, d269581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46887, d269581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46955 q = 1) (hb : d269582 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46955, d269582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46955, d269582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46885 q = 1) (hb : d269489 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, d269489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104285 q ha hb
    | true =>
      simp only [d46885, d269489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104287 q ha hb
  have h10 (q : Pattern) (ha : d46886 q = 1) (hb : d269490 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, d269490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46886, d269490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46887 q = 1) (hb : d269491 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, d269491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46887, d269491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46895 q = 1) (hb : d269511 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, d269511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104287 q ha hb
    | true =>
      simp only [d46895, d269511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104290 q ha hb
  have h13 (q : Pattern) (ha : d46896 q = 1) (hb : d269512 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, d269512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46896, d269512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46897 q = 1) (hb : d269513 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, d269513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46897, d269513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46898 q = 1) (hb : d269514 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, d269514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46898, d269514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46956 q = 1) (hb : d269583 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46956, d269583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46956, d269583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46957 q = 1) (hb : d269584 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46957, d269584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46957, d269584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro104316 (p : Pattern) (ha : d46963 p = 1) (hb : d269595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46958 q = 1) (hb : d269585 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46958, d269585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104315 q ha hb
    | true =>
      simp only [d46958, d269585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46959 q = 1) (hb : d269586 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46959, d269586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46959, d269586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46902 q = 1) (hb : d269590 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d269590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104300 q ha hb
    | true =>
      simp only [d46902, d269590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46903 q = 1) (hb : d269591 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d269591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d269591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46960 q = 1) (hb : d269592 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46960, d269592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46960, d269592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46961 q = 1) (hb : d269593 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46961, d269593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46961, d269593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46962 q = 1) (hb : d269594 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46962, d269594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46962, d269594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46963 q = 1) (hb : d269595 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46963, d269595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46963, d269595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104317 (p : Pattern) (ha : d47016 p = 1) (hb : d269608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269480 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d269482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104286 q ha hb
    | true =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46878 q = 1) (hb : d269483 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d46879 q = 1) (hb : d269484 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, d269484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46879, d269484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46880 q = 1) (hb : d269485 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, d269485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46880, d269485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d46881 q = 1) (hb : d269486 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, d269486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46881, d269486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d269607 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d47016 q = 1) (hb : d269608 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47016, d269608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47016, d269608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104318 (p : Pattern) (ha : d47022 p = 1) (hb : d269621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46885 q = 1) (hb : d269489 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, d269489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104285 q ha hb
    | true =>
      simp only [d46885, d269489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104287 q ha hb
  have h2 (q : Pattern) (ha : d46886 q = 1) (hb : d269490 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, d269490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46886, d269490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46887 q = 1) (hb : d269491 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, d269491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46887, d269491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46895 q = 1) (hb : d269511 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, d269511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104287 q ha hb
    | true =>
      simp only [d46895, d269511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104290 q ha hb
  have h5 (q : Pattern) (ha : d46896 q = 1) (hb : d269512 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, d269512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46896, d269512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46897 q = 1) (hb : d269513 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, d269513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46897, d269513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46898 q = 1) (hb : d269514 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, d269514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46898, d269514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d269615 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d47017 q = 1) (hb : d269616 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47017, d269616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104317 q ha hb
    | true =>
      simp only [d47017, d269616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d47018 q = 1) (hb : d269617 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47018, d269617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47018, d269617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d47019 q = 1) (hb : d269618 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47019, d269618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47019, d269618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d47020 q = 1) (hb : d269619 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47020, d269619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d47020, d269619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d47021 q = 1) (hb : d269620 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47021, d269620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47021, d269620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d47022 q = 1) (hb : d269621 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47022, d269621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d47022, d269621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro104319 (p : Pattern) (ha : d47028 p = 1) (hb : d269627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47023 q = 1) (hb : d269622 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47023, d269622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104318 q ha hb
    | true =>
      simp only [d47023, d269622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47024 q = 1) (hb : d269623 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47024, d269623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47024, d269623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47025 q = 1) (hb : d269624 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47025, d269624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47025, d269624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47026 q = 1) (hb : d269625 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47026, d269625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47026, d269625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47027 q = 1) (hb : d269626 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47027, d269626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47027, d269626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47028 q = 1) (hb : d269627 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47028, d269627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47028, d269627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104320 (p : Pattern) (ha : d269633 p = 1) (hb : d321686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46939 q = 1) (hb : d269560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46939, d269560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104310 q ha hb
    | true =>
      simp only [d46939, d269560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104311 q ha hb
  have h2 (q : Pattern) (ha : d46940 q = 1) (hb : d269561 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46940, d269561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46940, d269561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46941 q = 1) (hb : d269562 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46941, d269562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46941, d269562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46942 q = 1) (hb : d269563 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46942, d269563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46942, d269563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46949 q = 1) (hb : d269570 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46949, d269570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104312 q ha hb
    | true =>
      simp only [d46949, d269570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104313 q ha hb
  have h6 (q : Pattern) (ha : d46950 q = 1) (hb : d269571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46950, d269571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46950, d269571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46951 q = 1) (hb : d269572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46951, d269572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46951, d269572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46964 q = 1) (hb : d269600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46964, d269600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104316 q ha hb
    | true =>
      simp only [d46964, d269600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104301 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269537 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d269601 q = 1) (hb : d321682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269601, d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269601, d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d47029 q = 1) (hb : d269628 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47029, d269628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104319 q ha hb
    | true =>
      simp only [d47029, d269628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d47030 q = 1) (hb : d269629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47030, d269629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d47030, d269629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d269630 q = 1) (hb : d321683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269630, d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269630, d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d269631 q = 1) (hb : d321684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269631, d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d269631, d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269632 q = 1) (hb : d321685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269632, d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269632, d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269633 q = 1) (hb : d321686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269633, d321686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269633, d321686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro104321 (p : Pattern) (ha : d46924 p = 1) (hb : d269646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46902 q = 1) (hb : d269590 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d269590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104300 q ha hb
    | true =>
      simp only [d46902, d269590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46903 q = 1) (hb : d269591 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d269591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d269591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46908 q = 1) (hb : d269596 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d269596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, d269596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46909 q = 1) (hb : d269597 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, d269597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, d269597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46910 q = 1) (hb : d269598 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46910, d269598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46910, d269598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46924 q = 1) (hb : d269646 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46924, d269646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46924, d269646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104322 (p : Pattern) (ha : d47035 p = 1) (hb : d269634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46902 q = 1) (hb : d269523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d269523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104292 q ha hb
    | true =>
      simp only [d46902, d269523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46903 q = 1) (hb : d269524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d269524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d269524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46908 q = 1) (hb : d269529 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d269529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, d269529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46909 q = 1) (hb : d269530 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, d269530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, d269530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46935 q = 1) (hb : d269556 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46935, d269556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46935, d269556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47035 q = 1) (hb : d269634 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47035, d269634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47035, d269634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104323 (p : Pattern) (ha : d47036 p = 1) (hb : d269635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46912 q = 1) (hb : d269533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d269533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, d269533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46913 q = 1) (hb : d269534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, d269534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, d269534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46937 q = 1) (hb : d269558 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46937, d269558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46937, d269558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47036 q = 1) (hb : d269635 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47036, d269635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47036, d269635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104324 (p : Pattern) (ha : d47041 p = 1) (hb : d269640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46902 q = 1) (hb : d269523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d269523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104292 q ha hb
    | true =>
      simp only [d46902, d269523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46903 q = 1) (hb : d269524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d269524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d269524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46908 q = 1) (hb : d269529 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d269529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, d269529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46943 q = 1) (hb : d269564 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46943, d269564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46943, d269564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46944 q = 1) (hb : d269565 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46944, d269565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46944, d269565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47041 q = 1) (hb : d269640 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47041, d269640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47041, d269640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104325 (p : Pattern) (ha : d47042 p = 1) (hb : d269641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46906 q = 1) (hb : d269527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104293 q ha hb
    | true =>
      simp only [d46906, d269527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46907 q = 1) (hb : d269528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d269528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46912 q = 1) (hb : d269533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d269533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, d269533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46946 q = 1) (hb : d269567 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46946, d269567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46946, d269567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46947 q = 1) (hb : d269568 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46947, d269568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46947, d269568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47042 q = 1) (hb : d269641 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47042, d269641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47042, d269641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104326 (p : Pattern) (ha : d47046 p = 1) (hb : d269645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46958 q = 1) (hb : d269585 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46958, d269585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104315 q ha hb
    | true =>
      simp only [d46958, d269585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46959 q = 1) (hb : d269586 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46959, d269586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46959, d269586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46902 q = 1) (hb : d269590 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d269590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104300 q ha hb
    | true =>
      simp only [d46902, d269590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46903 q = 1) (hb : d269591 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d269591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d269591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46960 q = 1) (hb : d269592 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46960, d269592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46960, d269592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46961 q = 1) (hb : d269593 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46961, d269593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46961, d269593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46962 q = 1) (hb : d269594 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46962, d269594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46962, d269594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47046 q = 1) (hb : d269645 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47046, d269645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47046, d269645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104327 (p : Pattern) (ha : d47052 p = 1) (hb : d269649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47023 q = 1) (hb : d269622 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47023, d269622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104318 q ha hb
    | true =>
      simp only [d47023, d269622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47024 q = 1) (hb : d269623 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47024, d269623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47024, d269623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47025 q = 1) (hb : d269624 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47025, d269624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47025, d269624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47026 q = 1) (hb : d269625 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47026, d269625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47026, d269625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47027 q = 1) (hb : d269626 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47027, d269626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47027, d269626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47052 q = 1) (hb : d269649 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47052, d269649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47052, d269649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104328 (p : Pattern) (ha : d269655 p = 1) (hb : d321691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46939 q = 1) (hb : d269560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46939, d269560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104310 q ha hb
    | true =>
      simp only [d46939, d269560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104311 q ha hb
  have h2 (q : Pattern) (ha : d46940 q = 1) (hb : d269561 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46940, d269561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46940, d269561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46941 q = 1) (hb : d269562 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46941, d269562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46941, d269562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46942 q = 1) (hb : d269563 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46942, d269563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46942, d269563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46949 q = 1) (hb : d269570 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46949, d269570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104312 q ha hb
    | true =>
      simp only [d46949, d269570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104313 q ha hb
  have h6 (q : Pattern) (ha : d46950 q = 1) (hb : d269571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46950, d269571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46950, d269571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46951 q = 1) (hb : d269572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46951, d269572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46951, d269572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46964 q = 1) (hb : d269600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46964, d269600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104316 q ha hb
    | true =>
      simp only [d46964, d269600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104301 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269537 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d269601 q = 1) (hb : d321682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269601, d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269601, d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d47029 q = 1) (hb : d269628 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47029, d269628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104319 q ha hb
    | true =>
      simp only [d47029, d269628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d47030 q = 1) (hb : d269629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47030, d269629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d47030, d269629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d269630 q = 1) (hb : d321683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269630, d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269630, d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d269631 q = 1) (hb : d321684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269631, d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d269631, d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269632 q = 1) (hb : d321685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269632, d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269632, d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d47037 q = 1) (hb : d269636 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47037, d269636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104322 q ha hb
    | true =>
      simp only [d47037, d269636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104323 q ha hb
  have h17 (q : Pattern) (ha : d47038 q = 1) (hb : d269637 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47038, d269637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47038, d269637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d47039 q = 1) (hb : d269638 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47039, d269638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d47039, d269638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d47040 q = 1) (hb : d269639 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47040, d269639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47040, d269639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d47043 q = 1) (hb : d269642 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47043, d269642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104324 q ha hb
    | true =>
      simp only [d47043, d269642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104325 q ha hb
  have h21 (q : Pattern) (ha : d47044 q = 1) (hb : d269643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47044, d269643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47044, d269643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d47045 q = 1) (hb : d269644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47045, d269644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d47045, d269644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d47047 q = 1) (hb : d269647 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47047, d269647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104326 q ha hb
    | true =>
      simp only [d47047, d269647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104321 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d269547 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d269648 q = 1) (hb : d321687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269648, d321687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d269648, d321687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d47053 q = 1) (hb : d269650 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47053, d269650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104327 q ha hb
    | true =>
      simp only [d47053, d269650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d47054 q = 1) (hb : d269651 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47054, d269651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d47054, d269651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d269652 q = 1) (hb : d321688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269652, d321688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d269652, d321688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d269653 q = 1) (hb : d321689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269653, d321689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d269653, d321689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d269654 q = 1) (hb : d321690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269654, d321690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d269654, d321690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d269655 q = 1) (hb : d321691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269655, d321691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269655, d321691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro104329 (p : Pattern) (ha : d269680 p = 1) (hb : d321698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47047 q = 1) (hb : d269647 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47047, d269647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104326 q ha hb
    | true =>
      simp only [d47047, d269647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104321 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269547 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269648 q = 1) (hb : d321687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269648, d321687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269648, d321687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d47053 q = 1) (hb : d269650 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47053, d269650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104327 q ha hb
    | true =>
      simp only [d47053, d269650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47054 q = 1) (hb : d269651 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47054, d269651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47054, d269651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d269652 q = 1) (hb : d321688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269652, d321688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269652, d321688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d269678 q = 1) (hb : d321696 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269678, d321696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269678, d321696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269679 q = 1) (hb : d321697 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269679, d321697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269679, d321697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269680 q = 1) (hb : d321698 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269680, d321698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269680, d321698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro104330 (p : Pattern) (ha : d47091 p = 1) (hb : d269708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269702 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269691 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d47086 q = 1) (hb : d269703 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d269703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47086, d269703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104284 q ha hb
  have h4 (q : Pattern) (ha : d46877 q = 1) (hb : d269464 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104284 q ha hb
    | true =>
      simp only [d46877, d269464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d47087 q = 1) (hb : d269704 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d269704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47087, d269704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46878 q = 1) (hb : d269465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46878, d269465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d47088 q = 1) (hb : d269705 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d269705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47088, d269705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47089 q = 1) (hb : d269706 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d269706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47089, d269706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d47090 q = 1) (hb : d269707 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, d269707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47090, d269707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d47091 q = 1) (hb : d269708 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47091, d269708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47091, d269708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104331 (p : Pattern) (ha : d47096 p = 1) (hb : d269713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269691 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d47086 q = 1) (hb : d269703 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d269703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47086, d269703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104284 q ha hb
  have h3 (q : Pattern) (ha : d46877 q = 1) (hb : d269464 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104284 q ha hb
    | true =>
      simp only [d46877, d269464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d47087 q = 1) (hb : d269704 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d269704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47087, d269704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46878 q = 1) (hb : d269465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46878, d269465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d47088 q = 1) (hb : d269705 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d269705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47088, d269705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47089 q = 1) (hb : d269706 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d269706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47089, d269706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d47090 q = 1) (hb : d269707 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, d269707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47090, d269707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d47095 q = 1) (hb : d269712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, d269712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47095, d269712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d47096 q = 1) (hb : d269713 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47096, d269713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47096, d269713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104332 (p : Pattern) (ha : d47106 p = 1) (hb : d269741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47086 q = 1) (hb : d269731 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d269731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47086, d269731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104288 q ha hb
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d269496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104288 q ha hb
    | true =>
      simp only [d46877, d269496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47087 q = 1) (hb : d269732 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d269732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, d269732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46878 q = 1) (hb : d269497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d269497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47088 q = 1) (hb : d269733 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d269733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, d269733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47089 q = 1) (hb : d269734 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d269734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, d269734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47095 q = 1) (hb : d269735 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, d269735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, d269735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47101 q = 1) (hb : d269736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, d269736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47101, d269736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104289 q ha hb
  have h9 (q : Pattern) (ha : d46889 q = 1) (hb : d269505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, d269505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104289 q ha hb
    | true =>
      simp only [d46889, d269505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d47102 q = 1) (hb : d269737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, d269737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47102, d269737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46890 q = 1) (hb : d269506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, d269506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46890, d269506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d47103 q = 1) (hb : d269738 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47103, d269738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d47103, d269738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d47104 q = 1) (hb : d269739 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47104, d269739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d47104, d269739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d47105 q = 1) (hb : d269740 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47105, d269740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d47105, d269740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d47106 q = 1) (hb : d269741 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47106, d269741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47106, d269741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104333 (p : Pattern) (ha : d47112 p = 1) (hb : d269747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269693 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d47092 q = 1) (hb : d269709 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47092, d269709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47092, d269709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104330 q ha hb
  have h3 (q : Pattern) (ha : d47093 q = 1) (hb : d269710 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47093, d269710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47093, d269710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d47094 q = 1) (hb : d269711 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47094, d269711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47094, d269711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47097 q = 1) (hb : d269714 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, d269714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104330 q ha hb
    | true =>
      simp only [d47097, d269714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104331 q ha hb
  have h6 (q : Pattern) (ha : d47098 q = 1) (hb : d269715 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, d269715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47098, d269715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47099 q = 1) (hb : d269716 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, d269716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47099, d269716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47100 q = 1) (hb : d269717 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47100, d269717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47100, d269717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d47097 q = 1) (hb : d269728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, d269728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104330 q ha hb
    | true =>
      simp only [d47097, d269728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104305 q ha hb
  have h10 (q : Pattern) (ha : d47098 q = 1) (hb : d269729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, d269729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47098, d269729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d47099 q = 1) (hb : d269730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, d269730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47099, d269730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d47107 q = 1) (hb : d269742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d269742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104305 q ha hb
    | true =>
      simp only [d47107, d269742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104332 q ha hb
  have h13 (q : Pattern) (ha : d47108 q = 1) (hb : d269743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d269743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47108, d269743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d47109 q = 1) (hb : d269744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d269744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47109, d269744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d47110 q = 1) (hb : d269745 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, d269745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d47110, d269745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d47111 q = 1) (hb : d269746 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47111, d269746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47111, d269746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d47112 q = 1) (hb : d269747 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47112, d269747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d47112, d269747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro104334 (p : Pattern) (ha : d47117 p = 1) (hb : d269752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47097 q = 1) (hb : d269728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, d269728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104330 q ha hb
    | true =>
      simp only [d47097, d269728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104305 q ha hb
  have h2 (q : Pattern) (ha : d47098 q = 1) (hb : d269729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, d269729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47098, d269729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47099 q = 1) (hb : d269730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, d269730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47099, d269730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d47107 q = 1) (hb : d269742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d269742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104305 q ha hb
    | true =>
      simp only [d47107, d269742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104332 q ha hb
  have h5 (q : Pattern) (ha : d47108 q = 1) (hb : d269743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d269743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47108, d269743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47109 q = 1) (hb : d269744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d269744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47109, d269744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47110 q = 1) (hb : d269745 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, d269745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47110, d269745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47115 q = 1) (hb : d269750 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47115, d269750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47115, d269750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d47116 q = 1) (hb : d269751 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47116, d269751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47116, d269751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d47117 q = 1) (hb : d269752 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47117, d269752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d47117, d269752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro104335 (p : Pattern) (ha : d47123 p = 1) (hb : d269758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47113 q = 1) (hb : d269748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47113, d269748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104333 q ha hb
    | true =>
      simp only [d47113, d269748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47114 q = 1) (hb : d269749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47114, d269749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47114, d269749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47118 q = 1) (hb : d269753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47118, d269753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104334 q ha hb
    | true =>
      simp only [d47118, d269753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47119 q = 1) (hb : d269754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47119, d269754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47119, d269754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47120 q = 1) (hb : d269755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47120, d269755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47120, d269755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47121 q = 1) (hb : d269756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47121, d269756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47121, d269756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47122 q = 1) (hb : d269757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47122, d269757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47122, d269757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47123 q = 1) (hb : d269758 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47123, d269758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47123, d269758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104336 (p : Pattern) (ha : d47131 p = 1) (hb : d269772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47118 q = 1) (hb : d269753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47118, d269753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104334 q ha hb
    | true =>
      simp only [d47118, d269753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47119 q = 1) (hb : d269754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47119, d269754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47119, d269754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47126 q = 1) (hb : d269767 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47126, d269767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104307 q ha hb
    | true =>
      simp only [d47126, d269767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47127 q = 1) (hb : d269768 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47127, d269768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47127, d269768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47128 q = 1) (hb : d269769 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47128, d269769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47128, d269769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47129 q = 1) (hb : d269770 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47129, d269770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47129, d269770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47130 q = 1) (hb : d269771 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47130, d269771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47130, d269771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47131 q = 1) (hb : d269772 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47131, d269772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47131, d269772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104337 (p : Pattern) (ha : d47193 p = 1) (hb : d269815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d47086 q = 1) (hb : d269722 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d269722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47086, d269722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104286 q ha hb
  have h3 (q : Pattern) (ha : d46877 q = 1) (hb : d269482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104286 q ha hb
    | true =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d47087 q = 1) (hb : d269723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d269723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47087, d269723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46878 q = 1) (hb : d269483 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d47088 q = 1) (hb : d269724 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d269724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47088, d269724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47089 q = 1) (hb : d269725 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d269725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47089, d269725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d47090 q = 1) (hb : d269726 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, d269726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47090, d269726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269814 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d47193 q = 1) (hb : d269815 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47193, d269815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47193, d269815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104338 (p : Pattern) (ha : d47199 p = 1) (hb : d269827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47097 q = 1) (hb : d269728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, d269728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104330 q ha hb
    | true =>
      simp only [d47097, d269728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104305 q ha hb
  have h2 (q : Pattern) (ha : d47098 q = 1) (hb : d269729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, d269729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47098, d269729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47099 q = 1) (hb : d269730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, d269730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47099, d269730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d47107 q = 1) (hb : d269742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d269742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104305 q ha hb
    | true =>
      simp only [d47107, d269742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104332 q ha hb
  have h5 (q : Pattern) (ha : d47108 q = 1) (hb : d269743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d269743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47108, d269743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47109 q = 1) (hb : d269744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d269744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47109, d269744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47110 q = 1) (hb : d269745 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, d269745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47110, d269745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d269821 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d47194 q = 1) (hb : d269822 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47194, d269822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104337 q ha hb
    | true =>
      simp only [d47194, d269822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d47195 q = 1) (hb : d269823 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47195, d269823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47195, d269823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d47196 q = 1) (hb : d269824 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47196, d269824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47196, d269824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d47197 q = 1) (hb : d269825 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47197, d269825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d47197, d269825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d47198 q = 1) (hb : d269826 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47198, d269826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47198, d269826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d47199 q = 1) (hb : d269827 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47199, d269827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d47199, d269827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro104339 (p : Pattern) (ha : d47205 p = 1) (hb : d269833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47200 q = 1) (hb : d269828 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47200, d269828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104338 q ha hb
    | true =>
      simp only [d47200, d269828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47201 q = 1) (hb : d269829 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47201, d269829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47201, d269829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47202 q = 1) (hb : d269830 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47202, d269830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47202, d269830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47203 q = 1) (hb : d269831 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47203, d269831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47203, d269831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47204 q = 1) (hb : d269832 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47204, d269832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47204, d269832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47205 q = 1) (hb : d269833 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47205, d269833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47205, d269833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104340 (p : Pattern) (ha : d269839 p = 1) (hb : d321708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47132 q = 1) (hb : d269773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47132, d269773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104335 q ha hb
    | true =>
      simp only [d47132, d269773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104336 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269808 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269809 q = 1) (hb : d321704 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269809, d321704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269809, d321704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d47206 q = 1) (hb : d269834 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47206, d269834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104339 q ha hb
    | true =>
      simp only [d47206, d269834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47207 q = 1) (hb : d269835 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47207, d269835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47207, d269835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d269836 q = 1) (hb : d321705 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269836, d321705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269836, d321705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d269837 q = 1) (hb : d321706 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269837, d321706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269837, d321706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269838 q = 1) (hb : d321707 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269838, d321707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269838, d321707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269839 q = 1) (hb : d321708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269839, d321708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269839, d321708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro104341 (p : Pattern) (ha : d269856 p = 1) (hb : d321714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46922 q = 1) (hb : d269543 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46922, d269543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46922, d269543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104296 q ha hb
  have h2 (q : Pattern) (ha : d46923 q = 1) (hb : d269544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46923, d269544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46923, d269544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46932 q = 1) (hb : d269553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, d269553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104296 q ha hb
    | true =>
      simp only [d46932, d269553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104299 q ha hb
  have h4 (q : Pattern) (ha : d46933 q = 1) (hb : d269554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, d269554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46933, d269554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46934 q = 1) (hb : d269555 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46934, d269555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46934, d269555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269656 q = 1) (hb : d321692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269656, d321692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104320 q ha hb
    | true =>
      simp only [d269656, d321692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104328 q ha hb
  have h7 (q : Pattern) (ha : d47072 q = 1) (hb : d269674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47072, d269674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104302 q ha hb
    | true =>
      simp only [d47072, d269674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104303 q ha hb
  have h8 (q : Pattern) (ha : d269675 q = 1) (hb : d321693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269675, d321693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269675, d321693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d269676 q = 1) (hb : d321694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269676, d321694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269676, d321694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269677 q = 1) (hb : d321695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269677, d321695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d269677, d321695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269681 q = 1) (hb : d321699 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269681, d321699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269681, d321699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104329 q ha hb
  have h12 (q : Pattern) (ha : d47081 q = 1) (hb : d269683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47081, d269683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47081, d269683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104304 q ha hb
  have h13 (q : Pattern) (ha : d269684 q = 1) (hb : d321700 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269684, d321700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269684, d321700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d269685 q = 1) (hb : d321701 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269685, d321701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269685, d321701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269686 q = 1) (hb : d321702 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269686, d321702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269686, d321702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269687 q = 1) (hb : d321703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269687, d321703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269687, d321703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269840 q = 1) (hb : d321709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269840, d321709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269840, d321709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104340 q ha hb
  have h18 (q : Pattern) (ha : d47223 q = 1) (hb : d269851 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47223, d269851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47223, d269851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104309 q ha hb
  have h19 (q : Pattern) (ha : d269852 q = 1) (hb : d321710 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269852, d321710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269852, d321710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d269853 q = 1) (hb : d321711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269853, d321711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269853, d321711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269854 q = 1) (hb : d321712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269854, d321712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d269854, d321712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d269855 q = 1) (hb : d321713 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269855, d321713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269855, d321713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d269856 q = 1) (hb : d321714 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269856, d321714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269856, d321714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro104342 (p : Pattern) (ha : d269862 p = 1) (hb : d321720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269857 q = 1) (hb : d321715 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269857, d321715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269857, d321715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104341 q ha hb
  have h2 (q : Pattern) (ha : d269858 q = 1) (hb : d321716 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269858, d321716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269858, d321716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269859 q = 1) (hb : d321717 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269859, d321717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269859, d321717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269860 q = 1) (hb : d321718 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269860, d321718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269860, d321718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269861 q = 1) (hb : d321719 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269861, d321719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269861, d321719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269862 q = 1) (hb : d321720 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269862, d321720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269862, d321720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104343 (p : Pattern) (ha : d269868 p = 1) (hb : d326423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d268313 q = 1) (hb : d325771 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268313, d325771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104052 q ha hb
    | true =>
      simp only [d268313, d325771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104098 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268585 q = 1) (hb : d326044 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268585, d326044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268585, d326044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104151 q ha hb
  have h3 (q : Pattern) (ha : d268586 q = 1) (hb : d326045 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d268586, d326045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d268586, d326045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268956 q = 1) (hb : d326418 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268956, d326418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268956, d326418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104213 q ha hb
  have h5 (q : Pattern) (ha : d268957 q = 1) (hb : d326419 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d268957, d326419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268957, d326419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268958 q = 1) (hb : d326420 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d268958, d326420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268958, d326420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269422 q = 1) (hb : d324878 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d269422, d324878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269422, d324878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104282 q ha hb
  have h8 (q : Pattern) (ha : d269423 q = 1) (hb : d324879 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d269423, d324879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269423, d324879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269424 q = 1) (hb : d324880 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d269424, d324880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269424, d324880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269425 q = 1) (hb : d326421 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d269425, d326421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269425, d326421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269863 q = 1) (hb : d321721 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d269863, d321721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269863, d321721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104342 q ha hb
  have h12 (q : Pattern) (ha : d269864 q = 1) (hb : d321722 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d269864, d321722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269864, d321722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269865 q = 1) (hb : d321723 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d269865, d321723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269865, d321723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269866 q = 1) (hb : d321724 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d269866, d321724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269866, d321724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269867 q = 1) (hb : d326422 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d269867, d326422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269867, d326422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269868 q = 1) (hb : d326423 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d269868, d326423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269868, d326423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro104344 (p : Pattern) (ha : d269874 p = 1) (hb : d326429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269869 q = 1) (hb : d326424 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d269869, d326424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104343 q ha hb
    | true =>
      simp only [d269869, d326424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269870 q = 1) (hb : d326425 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d269870, d326425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269870, d326425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269871 q = 1) (hb : d326426 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d269871, d326426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269871, d326426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269872 q = 1) (hb : d326427 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d269872, d326427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269872, d326427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269873 q = 1) (hb : d326428 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d269873, d326428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269873, d326428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269874 q = 1) (hb : d326429 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d269874, d326429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269874, d326429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104345 (p : Pattern) (ha : d269880 p = 1) (hb : d326435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269875 q = 1) (hb : d326430 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d269875, d326430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104344 q ha hb
    | true =>
      simp only [d269875, d326430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269876 q = 1) (hb : d326431 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d269876, d326431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269876, d326431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269877 q = 1) (hb : d326432 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d269877, d326432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269877, d326432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269878 q = 1) (hb : d326433 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d269878, d326433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269878, d326433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269879 q = 1) (hb : d326434 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d269879, d326434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269879, d326434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269880 q = 1) (hb : d326435 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d269880, d326435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269880, d326435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104346 (p : Pattern) (ha : d269886 p = 1) (hb : d326441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269881 q = 1) (hb : d326436 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d269881, d326436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104345 q ha hb
    | true =>
      simp only [d269881, d326436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269882 q = 1) (hb : d326437 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d269882, d326437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269882, d326437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269883 q = 1) (hb : d326438 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d269883, d326438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269883, d326438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269884 q = 1) (hb : d326439 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d269884, d326439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269884, d326439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269885 q = 1) (hb : d326440 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d269885, d326440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269885, d326440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269886 q = 1) (hb : d326441 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d269886, d326441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269886, d326441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104347 (p : Pattern) (ha : d269892 p = 1) (hb : d326447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269887 q = 1) (hb : d326442 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d269887, d326442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104346 q ha hb
    | true =>
      simp only [d269887, d326442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269888 q = 1) (hb : d326443 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d269888, d326443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269888, d326443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269889 q = 1) (hb : d326444 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d269889, d326444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269889, d326444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269890 q = 1) (hb : d326445 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d269890, d326445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269890, d326445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269891 q = 1) (hb : d326446 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d269891, d326446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269891, d326446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269892 q = 1) (hb : d326447 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d269892, d326447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269892, d326447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104348 (p : Pattern) (ha : d269898 p = 1) (hb : d326453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269893 q = 1) (hb : d326448 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d269893, d326448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104347 q ha hb
    | true =>
      simp only [d269893, d326448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269894 q = 1) (hb : d326449 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d269894, d326449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269894, d326449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269895 q = 1) (hb : d326450 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d269895, d326450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269895, d326450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269896 q = 1) (hb : d326451 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d269896, d326451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269896, d326451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269897 q = 1) (hb : d326452 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d269897, d326452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269897, d326452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269898 q = 1) (hb : d326453 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d269898, d326453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269898, d326453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104349 (p : Pattern) (ha : d269904 p = 1) (hb : d326459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269899 q = 1) (hb : d326454 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d269899, d326454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104348 q ha hb
    | true =>
      simp only [d269899, d326454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269900 q = 1) (hb : d326455 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d269900, d326455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269900, d326455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269901 q = 1) (hb : d326456 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d269901, d326456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269901, d326456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269902 q = 1) (hb : d326457 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d269902, d326457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269902, d326457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269903 q = 1) (hb : d326458 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d269903, d326458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269903, d326458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269904 q = 1) (hb : d326459 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d269904, d326459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269904, d326459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104350 (p : Pattern) (ha : d269910 p = 1) (hb : d326465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269905 q = 1) (hb : d326460 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d269905, d326460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104349 q ha hb
    | true =>
      simp only [d269905, d326460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269906 q = 1) (hb : d326461 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d269906, d326461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269906, d326461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269907 q = 1) (hb : d326462 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d269907, d326462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269907, d326462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269908 q = 1) (hb : d326463 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d269908, d326463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269908, d326463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269909 q = 1) (hb : d326464 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d269909, d326464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269909, d326464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269910 q = 1) (hb : d326465 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d269910, d326465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269910, d326465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104351 (p : Pattern) (ha : d321880 p = 1) (hb : d325306 p = 1) : d325181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46532 q = 1) (hb : d325306 q = 1) : d324666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103757 q ha hb
    | true =>
      simp only [d46532, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103758 q ha hb
  have h2 (q : Pattern) (ha : d46533 q = 1) (hb : d325306 q = 1) : d324667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46533, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46534 q = 1) (hb : d325306 q = 1) : d324668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46534, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46535 q = 1) (hb : d325306 q = 1) : d324669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46535, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46536 q = 1) (hb : d325306 q = 1) : d324670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46536, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321880 q = 1) (hb : d325306 q = 1) : d325181 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321880, d325181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321880, d325181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104352 (p : Pattern) (ha : d321891 p = 1) (hb : d325306 p = 1) : d325192 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321886 q = 1) (hb : d325306 q = 1) : d325187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d321886, d325187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103794 q ha hb
    | true =>
      simp only [d321886, d325187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103766 q ha hb
  have h2 (q : Pattern) (ha : d321887 q = 1) (hb : d325306 q = 1) : d325188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321887, d325188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321887, d325188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d321888 q = 1) (hb : d325306 q = 1) : d325189 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321888, d325189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321888, d325189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d321889 q = 1) (hb : d325306 q = 1) : d325190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321889, d325190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321889, d325190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d321890 q = 1) (hb : d325306 q = 1) : d325191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321890, d325191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321890, d325191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321891 q = 1) (hb : d325306 q = 1) : d325192 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321891, d325192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321891, d325192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104353 (p : Pattern) (ha : d321897 p = 1) (hb : d325306 p = 1) : d325198 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46538 q = 1) (hb : d325306 q = 1) : d324672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103756 q ha hb
    | true =>
      simp only [d46538, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103759 q ha hb
  have h2 (q : Pattern) (ha : d46539 q = 1) (hb : d325306 q = 1) : d324673 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46539, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321878 q = 1) (hb : d325306 q = 1) : d325179 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321878, d325179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321878, d325179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d321879 q = 1) (hb : d325306 q = 1) : d325180 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321879, d325180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321879, d325180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d321881 q = 1) (hb : d325306 q = 1) : d325182 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321881, d325182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321881, d325182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104351 q ha hb
  have h6 (q : Pattern) (ha : d321882 q = 1) (hb : d325306 q = 1) : d325183 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321882, d325183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321882, d325183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d321883 q = 1) (hb : d325306 q = 1) : d325184 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321883, d325184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321883, d325184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d321884 q = 1) (hb : d325306 q = 1) : d325185 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321884, d325185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321884, d325185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d321885 q = 1) (hb : d325306 q = 1) : d325186 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321885, d325186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321885, d325186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d321892 q = 1) (hb : d325306 q = 1) : d325193 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321892, d325193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321892, d325193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104352 q ha hb
  have h11 (q : Pattern) (ha : d321893 q = 1) (hb : d325306 q = 1) : d325194 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321893, d325194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321893, d325194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d321894 q = 1) (hb : d325306 q = 1) : d325195 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321894, d325195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d321894, d325195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d321895 q = 1) (hb : d325306 q = 1) : d325196 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321895, d325196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d321895, d325196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d321896 q = 1) (hb : d325306 q = 1) : d325197 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321896, d325197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321896, d325197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d321897 q = 1) (hb : d325306 q = 1) : d325198 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321897, d325198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321897, d325198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104354 (p : Pattern) (ha : d321903 p = 1) (hb : d325306 p = 1) : d325204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321898 q = 1) (hb : d325306 q = 1) : d325199 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321898, d325199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321898, d325199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104353 q ha hb
  have h2 (q : Pattern) (ha : d321899 q = 1) (hb : d325306 q = 1) : d325200 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321899, d325200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321899, d325200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d321900 q = 1) (hb : d325306 q = 1) : d325201 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321900, d325201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321900, d325201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d321901 q = 1) (hb : d325306 q = 1) : d325202 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321901, d325202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321901, d325202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d321902 q = 1) (hb : d325306 q = 1) : d325203 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321902, d325203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321902, d325203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321903 q = 1) (hb : d325306 q = 1) : d325204 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321903, d325204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321903, d325204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104355 (p : Pattern) (ha : d325306 p = 1) (hb : d367603 p = 1) : d326468 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d325306 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44916 q = 1) (hb : d325306 q = 1) : d325339 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d325339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103808 q ha hb
    | true =>
      simp only [d44916, d325339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44976 q = 1) (hb : d325306 q = 1) : d325399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44976, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44976, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44977 q = 1) (hb : d325306 q = 1) : d325400 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44977, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44977, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44978 q = 1) (hb : d325306 q = 1) : d325401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44978, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44978, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44979 q = 1) (hb : d325306 q = 1) : d325402 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44979, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44979, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d325306 q = 1) (hb : d367603 q = 1) : d326468 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367603, d326468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367603, d326468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro104356 (p : Pattern) (ha : d325306 p = 1) (hb : d367613 p = 1) : d326478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d325306 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44952 q = 1) (hb : d325306 q = 1) : d325375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44952, d325375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103813 q ha hb
    | true =>
      simp only [d44952, d325375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367609 q = 1) : d326474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367609, d326474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367609, d326474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367610 q = 1) : d326475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367610, d326475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367610, d326475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367611 q = 1) : d326476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367611, d326476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367611, d326476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367612 q = 1) : d326477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367612, d326477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367612, d326477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d325306 q = 1) (hb : d367613 q = 1) : d326478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367613, d326478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367613, d326478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro104357 (p : Pattern) (ha : d325306 p = 1) (hb : d367619 p = 1) : d326484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44981 q = 1) (hb : d325306 q = 1) : d325404 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44981, d325404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103816 q ha hb
    | true =>
      simp only [d44981, d325404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103817 q ha hb
  have h2 (q : Pattern) (ha : d44982 q = 1) (hb : d325306 q = 1) : d325405 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44982, d325405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44982, d325405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367601 q = 1) : d326466 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367601, d326466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d367601, d326466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367602 q = 1) : d326467 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367602, d326467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367602, d326467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367604 q = 1) : d326469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367604, d326469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367604, d326469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104355 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367605 q = 1) : d326470 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367605, d326470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367605, d326470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d325306 q = 1) (hb : d367606 q = 1) : d326471 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367606, d326471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367606, d326471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d325306 q = 1) (hb : d367607 q = 1) : d326472 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367607, d326472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367607, d326472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d325306 q = 1) (hb : d367608 q = 1) : d326473 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367608, d326473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367608, d326473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d325306 q = 1) (hb : d367614 q = 1) : d326479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367614, d326479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367614, d326479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104356 q ha hb
  have h11 (q : Pattern) (ha : d325306 q = 1) (hb : d367615 q = 1) : d326480 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367615, d326480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367615, d326480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d325306 q = 1) (hb : d367616 q = 1) : d326481 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367616, d326481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367616, d326481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d325306 q = 1) (hb : d367617 q = 1) : d326482 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367617, d326482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367617, d326482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d325306 q = 1) (hb : d367618 q = 1) : d326483 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367618, d326483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367618, d326483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d325306 q = 1) (hb : d367619 q = 1) : d326484 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367619, d326484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367619, d326484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104358 (p : Pattern) (ha : d325306 p = 1) (hb : d367625 p = 1) : d326490 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d325306 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367620 q = 1) : d326485 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367620, d326485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367620, d326485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104357 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367621 q = 1) : d326486 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367621, d326486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367621, d326486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367622 q = 1) : d326487 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367622, d326487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367622, d326487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367623 q = 1) : d326488 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367623, d326488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367623, d326488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367624 q = 1) : d326489 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367624, d326489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367624, d326489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d325306 q = 1) (hb : d367625 q = 1) : d326490 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367625, d326490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367625, d326490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro104359 (p : Pattern) (ha : d325306 p = 1) (hb : d367628 p = 1) : d326493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45200 q = 1) (hb : d325306 q = 1) : d325568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45200, d325568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103847 q ha hb
    | true =>
      simp only [d45200, d325568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103848 q ha hb
  have h2 (q : Pattern) (ha : d45201 q = 1) (hb : d325306 q = 1) : d325569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45201, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45201, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45202 q = 1) (hb : d325306 q = 1) : d325570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45202, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45202, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45203 q = 1) (hb : d325306 q = 1) : d325571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45203, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45203, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45204 q = 1) (hb : d325306 q = 1) : d325572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45204, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45204, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367628 q = 1) : d326493 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367628, d326493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367628, d326493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro104360 (p : Pattern) (ha : d325306 p = 1) (hb : d367639 p = 1) : d326504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367634 q = 1) : d326499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367634, d326499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103884 q hb ha
    | true =>
      simp only [d367634, d326499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103854 q hb ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367635 q = 1) : d326500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367635, d326500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367635, d326500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367636 q = 1) : d326501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367636, d326501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367636, d326501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367637 q = 1) : d326502 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367637, d326502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367637, d326502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367638 q = 1) : d326503 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367638, d326503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367638, d326503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367639 q = 1) : d326504 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367639, d326504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367639, d326504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104361 (p : Pattern) (ha : d325306 p = 1) (hb : d367645 p = 1) : d326510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45206 q = 1) (hb : d325306 q = 1) : d325574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45206, d325574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103846 q ha hb
    | true =>
      simp only [d45206, d325574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103849 q ha hb
  have h2 (q : Pattern) (ha : d45207 q = 1) (hb : d325306 q = 1) : d325575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45207, d325575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45207, d325575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367626 q = 1) : d326491 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367626, d326491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d367626, d326491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367627 q = 1) : d326492 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367627, d326492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367627, d326492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367629 q = 1) : d326494 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367629, d326494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367629, d326494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104359 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367630 q = 1) : d326495 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367630, d326495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367630, d326495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d325306 q = 1) (hb : d367631 q = 1) : d326496 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367631, d326496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367631, d326496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d325306 q = 1) (hb : d367632 q = 1) : d326497 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367632, d326497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367632, d326497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d325306 q = 1) (hb : d367633 q = 1) : d326498 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367633, d326498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367633, d326498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d325306 q = 1) (hb : d367640 q = 1) : d326505 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367640, d326505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367640, d326505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104360 q ha hb
  have h11 (q : Pattern) (ha : d325306 q = 1) (hb : d367641 q = 1) : d326506 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367641, d326506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367641, d326506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d325306 q = 1) (hb : d367642 q = 1) : d326507 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367642, d326507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367642, d326507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d325306 q = 1) (hb : d367643 q = 1) : d326508 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367643, d326508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367643, d326508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d325306 q = 1) (hb : d367644 q = 1) : d326509 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367644, d326509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367644, d326509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d325306 q = 1) (hb : d367645 q = 1) : d326510 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367645, d326510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367645, d326510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104362 (p : Pattern) (ha : d325306 p = 1) (hb : d367651 p = 1) : d326516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367646 q = 1) : d326511 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367646, d326511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367646, d326511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104361 q ha hb
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367647 q = 1) : d326512 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367647, d326512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367647, d326512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367648 q = 1) : d326513 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367648, d326513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367648, d326513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367649 q = 1) : d326514 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367649, d326514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367649, d326514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367650 q = 1) : d326515 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367650, d326515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367650, d326515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367651 q = 1) : d326516 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367651, d326516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367651, d326516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104363 (p : Pattern) (ha : d325306 p = 1) (hb : d367655 p = 1) : d326520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45542 q = 1) (hb : d325306 q = 1) : d325817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45542, d325817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103898 q ha hb
    | true =>
      simp only [d45542, d325817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103899 q ha hb
  have h2 (q : Pattern) (ha : d45543 q = 1) (hb : d325306 q = 1) : d325818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45543, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45543, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45544 q = 1) (hb : d325306 q = 1) : d325819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45544, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45544, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45545 q = 1) (hb : d325306 q = 1) : d325820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45545, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45545, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45546 q = 1) (hb : d325306 q = 1) : d325821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45546, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45546, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367655 q = 1) : d326520 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367655, d326520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367655, d326520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro104364 (p : Pattern) (ha : d325306 p = 1) (hb : d367666 p = 1) : d326531 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367661 q = 1) : d326526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367661, d326526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103937 q hb ha
    | true =>
      simp only [d367661, d326526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103907 q hb ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367662 q = 1) : d326527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367662, d326527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367662, d326527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367663 q = 1) : d326528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367663, d326528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367663, d326528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367664 q = 1) : d326529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367664, d326529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367664, d326529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367665 q = 1) : d326530 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367665, d326530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367665, d326530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367666 q = 1) : d326531 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367666, d326531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367666, d326531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104365 (p : Pattern) (ha : d325306 p = 1) (hb : d367672 p = 1) : d326537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45548 q = 1) (hb : d325306 q = 1) : d325823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45548, d325823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103897 q ha hb
    | true =>
      simp only [d45548, d325823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103900 q ha hb
  have h2 (q : Pattern) (ha : d45549 q = 1) (hb : d325306 q = 1) : d325824 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45549, d325824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45549, d325824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367653 q = 1) : d326518 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367653, d326518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d367653, d326518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367654 q = 1) : d326519 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367654, d326519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367654, d326519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367656 q = 1) : d326521 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367656, d326521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367656, d326521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104363 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367657 q = 1) : d326522 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367657, d326522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367657, d326522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d325306 q = 1) (hb : d367658 q = 1) : d326523 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367658, d326523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367658, d326523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d325306 q = 1) (hb : d367659 q = 1) : d326524 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367659, d326524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367659, d326524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d325306 q = 1) (hb : d367660 q = 1) : d326525 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367660, d326525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367660, d326525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d325306 q = 1) (hb : d367667 q = 1) : d326532 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367667, d326532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367667, d326532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104364 q ha hb
  have h11 (q : Pattern) (ha : d325306 q = 1) (hb : d367668 q = 1) : d326533 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367668, d326533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367668, d326533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d325306 q = 1) (hb : d367669 q = 1) : d326534 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367669, d326534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367669, d326534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d325306 q = 1) (hb : d367670 q = 1) : d326535 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367670, d326535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367670, d326535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d325306 q = 1) (hb : d367671 q = 1) : d326536 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367671, d326536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367671, d326536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d325306 q = 1) (hb : d367672 q = 1) : d326537 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367672, d326537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367672, d326537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104366 (p : Pattern) (ha : d325306 p = 1) (hb : d367678 p = 1) : d326543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367673 q = 1) : d326538 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367673, d326538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367673, d326538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104365 q ha hb
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367674 q = 1) : d326539 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367674, d326539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367674, d326539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367675 q = 1) : d326540 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367675, d326540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367675, d326540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367676 q = 1) : d326541 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367676, d326541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367676, d326541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367677 q = 1) : d326542 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367677, d326542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367677, d326542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367678 q = 1) : d326543 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367678, d326543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367678, d326543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104367 (p : Pattern) (ha : d325306 p = 1) (hb : d367683 p = 1) : d326548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46006 q = 1) (hb : d325306 q = 1) : d326145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46006, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103956 q ha hb
    | true =>
      simp only [d46006, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103957 q ha hb
  have h2 (q : Pattern) (ha : d46007 q = 1) (hb : d325306 q = 1) : d326146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46007, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46007, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46008 q = 1) (hb : d325306 q = 1) : d326147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46008, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46008, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46009 q = 1) (hb : d325306 q = 1) : d326148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46009, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46009, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46010 q = 1) (hb : d325306 q = 1) : d326149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46010, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46010, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367683 q = 1) : d326548 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367683, d326548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367683, d326548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro104368 (p : Pattern) (ha : d325306 p = 1) (hb : d367694 p = 1) : d326559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367689 q = 1) : d326554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367689, d326554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103998 q hb ha
    | true =>
      simp only [d367689, d326554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103965 q hb ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367690 q = 1) : d326555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367690, d326555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367690, d326555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367691 q = 1) : d326556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367691, d326556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367691, d326556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367692 q = 1) : d326557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367692, d326557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367692, d326557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367693 q = 1) : d326558 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367693, d326558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367693, d326558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367694 q = 1) : d326559 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367694, d326559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367694, d326559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104369 (p : Pattern) (ha : d325306 p = 1) (hb : d367700 p = 1) : d326565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46012 q = 1) (hb : d325306 q = 1) : d326151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46012, d326151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103955 q ha hb
    | true =>
      simp only [d46012, d326151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103958 q ha hb
  have h2 (q : Pattern) (ha : d46013 q = 1) (hb : d325306 q = 1) : d326152 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46013, d326152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46013, d326152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367681 q = 1) : d326546 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367681, d326546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d367681, d326546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367682 q = 1) : d326547 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367682, d326547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367682, d326547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367684 q = 1) : d326549 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367684, d326549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367684, d326549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104367 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367685 q = 1) : d326550 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367685, d326550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367685, d326550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d325306 q = 1) (hb : d367686 q = 1) : d326551 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367686, d326551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367686, d326551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d325306 q = 1) (hb : d367687 q = 1) : d326552 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367687, d326552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367687, d326552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d325306 q = 1) (hb : d367688 q = 1) : d326553 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367688, d326553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367688, d326553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d325306 q = 1) (hb : d367695 q = 1) : d326560 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367695, d326560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367695, d326560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104368 q ha hb
  have h11 (q : Pattern) (ha : d325306 q = 1) (hb : d367696 q = 1) : d326561 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367696, d326561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367696, d326561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d325306 q = 1) (hb : d367697 q = 1) : d326562 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367697, d326562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367697, d326562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d325306 q = 1) (hb : d367698 q = 1) : d326563 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367698, d326563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367698, d326563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d325306 q = 1) (hb : d367699 q = 1) : d326564 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367699, d326564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367699, d326564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d325306 q = 1) (hb : d367700 q = 1) : d326565 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367700, d326565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367700, d326565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104370 (p : Pattern) (ha : d325306 p = 1) (hb : d367706 p = 1) : d326571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367701 q = 1) : d326566 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367701, d326566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367701, d326566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104369 q ha hb
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367702 q = 1) : d326567 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367702, d326567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367702, d326567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367703 q = 1) : d326568 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367703, d326568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367703, d326568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367704 q = 1) : d326569 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367704, d326569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367704, d326569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367705 q = 1) : d326570 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367705, d326570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367705, d326570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367706 q = 1) : d326571 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367706, d326571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367706, d326571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104371 (p : Pattern) (ha : d325306 p = 1) (hb : d367712 p = 1) : d326623 p = 1 := by
  have h0 (q : Pattern) (ha : d325306 q = 1) (hb : d367652 q = 1) : d326517 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367652, d326517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104358 q ha hb
    | true =>
      simp only [d367652, d326517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104362 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367679 q = 1) : d326544 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367679, d326544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367679, d326544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104366 q ha hb
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367680 q = 1) : d326545 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d367680, d326545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d367680, d326545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367707 q = 1) : d326572 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367707, d326572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367707, d326572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104370 q ha hb
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367708 q = 1) : d326573 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d367708, d326573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367708, d326573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367709 q = 1) : d326574 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d367709, d326574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367709, d326574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321904 q = 1) (hb : d325306 q = 1) : d325205 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321904, d325205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321904, d325205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104354 q ha hb
  have h8 (q : Pattern) (ha : d321905 q = 1) (hb : d325306 q = 1) : d325206 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321905, d325206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321905, d325206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d321906 q = 1) (hb : d325306 q = 1) : d325207 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321906, d325207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321906, d325207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d325306 q = 1) (hb : d367710 q = 1) : d326575 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d367710, d326575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367710, d326575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d325306 q = 1) (hb : d326621 q = 1) : d326621 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d325306 q = 1) (hb : d367711 q = 1) : d326622 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d367711, d326622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367711, d326622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d325306 q = 1) (hb : d367712 q = 1) : d326623 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d367712, d326623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367712, d326623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h13 p ha hb
theorem andIntro104372 (p : Pattern) (ha : d325306 p = 1) (hb : d367718 p = 1) : d326629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367713 q = 1) : d326624 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d367713, d326624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104371 q ha hb
    | true =>
      simp only [d367713, d326624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367714 q = 1) : d326625 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d367714, d326625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367714, d326625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367715 q = 1) : d326626 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d367715, d326626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367715, d326626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367716 q = 1) : d326627 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d367716, d326627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367716, d326627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367717 q = 1) : d326628 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d367717, d326628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367717, d326628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367718 q = 1) : d326629 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d367718, d326629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367718, d326629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104373 (p : Pattern) (ha : d325306 p = 1) (hb : d367724 p = 1) : d326635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367719 q = 1) : d326630 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d367719, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104372 q ha hb
    | true =>
      simp only [d367719, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367720 q = 1) : d326631 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d367720, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367720, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367721 q = 1) : d326632 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d367721, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367721, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367722 q = 1) : d326633 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d367722, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367722, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367723 q = 1) : d326634 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d367723, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367723, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367724 q = 1) : d326635 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d367724, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367724, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104374 (p : Pattern) (ha : d325306 p = 1) (hb : d367730 p = 1) : d326641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367725 q = 1) : d326636 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d367725, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104373 q ha hb
    | true =>
      simp only [d367725, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367726 q = 1) : d326637 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d367726, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367726, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367727 q = 1) : d326638 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d367727, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367727, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367728 q = 1) : d326639 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d367728, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367728, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367729 q = 1) : d326640 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d367729, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367729, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367730 q = 1) : d326641 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d367730, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367730, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104375 (p : Pattern) (ha : d325306 p = 1) (hb : d367736 p = 1) : d326647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367731 q = 1) : d326642 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d367731, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104374 q ha hb
    | true =>
      simp only [d367731, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367732 q = 1) : d326643 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d367732, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367732, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367733 q = 1) : d326644 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d367733, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367733, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367734 q = 1) : d326645 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d367734, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367734, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367735 q = 1) : d326646 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d367735, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367735, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367736 q = 1) : d326647 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d367736, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367736, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104376 (p : Pattern) (ha : d325306 p = 1) (hb : d367742 p = 1) : d326653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367737 q = 1) : d326648 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d367737, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104375 q ha hb
    | true =>
      simp only [d367737, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367738 q = 1) : d326649 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d367738, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367738, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367739 q = 1) : d326650 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d367739, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367739, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367740 q = 1) : d326651 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d367740, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367740, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367741 q = 1) : d326652 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d367741, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367741, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367742 q = 1) : d326653 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d367742, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367742, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104377 (p : Pattern) (ha : d325306 p = 1) (hb : d367748 p = 1) : d326659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367743 q = 1) : d326654 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d367743, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104376 q ha hb
    | true =>
      simp only [d367743, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367744 q = 1) : d326655 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d367744, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367744, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367745 q = 1) : d326656 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d367745, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367745, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367746 q = 1) : d326657 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d367746, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367746, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367747 q = 1) : d326658 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d367747, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367747, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367748 q = 1) : d326659 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d367748, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367748, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104378 (p : Pattern) (ha : d325306 p = 1) (hb : d367754 p = 1) : d326665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325306 q = 1) (hb : d367749 q = 1) : d326660 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d367749, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104377 q ha hb
    | true =>
      simp only [d367749, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d325306 q = 1) (hb : d367750 q = 1) : d326661 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d367750, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367750, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d325306 q = 1) (hb : d367751 q = 1) : d326662 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d367751, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367751, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d325306 q = 1) (hb : d367752 q = 1) : d326663 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d367752, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367752, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d325306 q = 1) (hb : d367753 q = 1) : d326664 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d367753, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367753, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d325306 q = 1) (hb : d367754 q = 1) : d326665 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d367754, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367754, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104379 (p : Pattern) (ha : d267996 p = 1) (hb : d325396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d267946 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267952 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d267985 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d267866 q = 1) (hb : d325332 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d267866, d325332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104017 q ha hb
    | true =>
      simp only [d267866, d325332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d267986 q = 1) (hb : d325392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d267986, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d267986, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d267992 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d267993 q = 1) (hb : d325393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d267993, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d267993, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d267994 q = 1) (hb : d325394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d267994, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d267994, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d267995 q = 1) (hb : d325395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d267995, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d267995, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d267996 q = 1) (hb : d325396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d267996, d325396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d267996, d325396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104380 (p : Pattern) (ha : d268015 p = 1) (hb : d325403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267946 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d267952 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d267866 q = 1) (hb : d325332 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d267866, d325332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104017 q ha hb
    | true =>
      simp only [d267866, d325332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d267986 q = 1) (hb : d325392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d267986, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d267986, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d267992 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d267993 q = 1) (hb : d325393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d267993, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d267993, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d267994 q = 1) (hb : d325394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d267994, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d267994, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d267995 q = 1) (hb : d325395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d267995, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d267995, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d268001 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d268005 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d268007 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d267873 q = 1) (hb : d325339 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d267873, d325339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104019 q ha hb
    | true =>
      simp only [d267873, d325339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d268008 q = 1) (hb : d325399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268008, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d268008, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268011 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268012 q = 1) (hb : d325400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268012, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268012, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268013 q = 1) (hb : d325401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268013, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d268013, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d268014 q = 1) (hb : d325402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268014, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d268014, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d268015 q = 1) (hb : d325403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268015, d325403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d268015, d325403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104381 (p : Pattern) (ha : d268024 p = 1) (hb : d326468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d267873 q = 1) (hb : d325339 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d267873, d325339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104019 q ha hb
    | true =>
      simp only [d267873, d325339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d268008 q = 1) (hb : d325399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268008, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268008, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268011 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268012 q = 1) (hb : d325400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268012, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268012, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268022 q = 1) (hb : d325401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268022, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268022, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268023 q = 1) (hb : d325402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268023, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268023, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268024 q = 1) (hb : d326468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268024, d326468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268024, d326468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104382 (p : Pattern) (ha : d268064 p = 1) (hb : d326478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d267909 q = 1) (hb : d325375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d267909, d325375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104024 q ha hb
    | true =>
      simp only [d267909, d325375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d268054 q = 1) (hb : d326474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268054, d326474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268054, d326474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268060 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268061 q = 1) (hb : d326475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268061, d326475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268061, d326475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268062 q = 1) (hb : d326476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268062, d326476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268062, d326476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268063 q = 1) (hb : d326477 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268063, d326477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268063, d326477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268064 q = 1) (hb : d326478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268064, d326478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268064, d326478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104383 (p : Pattern) (ha : d268070 p = 1) (hb : d326484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267940 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268016 q = 1) (hb : d325404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268016, d325404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104379 q ha hb
    | true =>
      simp only [d268016, d325404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104380 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268018 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268019 q = 1) (hb : d325405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268019, d325405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d268019, d325405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268020 q = 1) (hb : d326466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268020, d326466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268020, d326466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268021 q = 1) (hb : d326467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268021, d326467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268021, d326467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268025 q = 1) (hb : d326469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268025, d326469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268025, d326469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104381 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d268026 q = 1) (hb : d326470 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268026, d326470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268026, d326470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268027 q = 1) (hb : d326471 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268027, d326471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268027, d326471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d268028 q = 1) (hb : d326472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268028, d326472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268028, d326472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d268029 q = 1) (hb : d326473 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268029, d326473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d268029, d326473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d268065 q = 1) (hb : d326479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268065, d326479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268065, d326479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104382 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268066 q = 1) (hb : d326480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268066, d326480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268066, d326480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268067 q = 1) (hb : d326481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268067, d326481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268067, d326481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d268068 q = 1) (hb : d326482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268068, d326482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d268068, d326482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d268069 q = 1) (hb : d326483 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268069, d326483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d268069, d326483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d268070 q = 1) (hb : d326484 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d268070, d326484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d268070, d326484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104384 (p : Pattern) (ha : d268076 p = 1) (hb : d326490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d267921 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d267921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d267921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68632 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d267922 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d267922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d267922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d267923 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d267923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d267923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d267924 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d267924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d267924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d267925 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d267925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d267925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268071 q = 1) (hb : d326485 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d268071, d326485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268071, d326485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104383 q ha hb
  have h8 (q : Pattern) (ha : d268072 q = 1) (hb : d326486 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d268072, d326486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268072, d326486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d268073 q = 1) (hb : d326487 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d268073, d326487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268073, d326487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d268074 q = 1) (hb : d326488 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d268074, d326488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268074, d326488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d268075 q = 1) (hb : d326489 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d268075, d326489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268075, d326489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d268076 q = 1) (hb : d326490 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d268076, d326490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d268076, d326490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro104385 (p : Pattern) (ha : d268184 p = 1) (hb : d325563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d268173 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d268094 q = 1) (hb : d325558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268094, d325558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104055 q ha hb
    | true =>
      simp only [d268094, d325558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104056 q ha hb
  have h5 (q : Pattern) (ha : d268174 q = 1) (hb : d325559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268174, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d268174, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d268180 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d268181 q = 1) (hb : d325560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268181, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d268181, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d268182 q = 1) (hb : d325561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268182, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d268182, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d268183 q = 1) (hb : d325562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268183, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268183, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d268184 q = 1) (hb : d325563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268184, d325563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268184, d325563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104386 (p : Pattern) (ha : d268205 p = 1) (hb : d325573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268173 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268094 q = 1) (hb : d325558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268094, d325558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104055 q ha hb
    | true =>
      simp only [d268094, d325558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104056 q ha hb
  have h4 (q : Pattern) (ha : d268174 q = 1) (hb : d325559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268174, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d268174, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d268180 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d268181 q = 1) (hb : d325560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268181, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d268181, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d268182 q = 1) (hb : d325561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268182, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268182, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268183 q = 1) (hb : d325562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268183, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268183, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d268190 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d268195 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d268197 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d268104 q = 1) (hb : d325568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268104, d325568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104058 q ha hb
    | true =>
      simp only [d268104, d325568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104059 q ha hb
  have h13 (q : Pattern) (ha : d268198 q = 1) (hb : d325569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268198, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d268198, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268201 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268202 q = 1) (hb : d325570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268202, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268202, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268203 q = 1) (hb : d325571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268203, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d268203, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d268204 q = 1) (hb : d325572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268204, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d268204, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d268205 q = 1) (hb : d325573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268205, d325573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d268205, d325573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104387 (p : Pattern) (ha : d268225 p = 1) (hb : d326493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268197 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268104 q = 1) (hb : d325568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268104, d325568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104058 q ha hb
    | true =>
      simp only [d268104, d325568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104059 q ha hb
  have h3 (q : Pattern) (ha : d268198 q = 1) (hb : d325569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268198, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268198, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268201 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268202 q = 1) (hb : d325570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268202, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268202, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268223 q = 1) (hb : d325571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268223, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268223, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268224 q = 1) (hb : d325572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268224, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268224, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268225 q = 1) (hb : d326493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268225, d326493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268225, d326493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104388 (p : Pattern) (ha : d268293 p = 1) (hb : d326504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268282 q = 1) (hb : d326499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268282, d326499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104092 q ha hb
    | true =>
      simp only [d268282, d326499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104095 q ha hb
  have h3 (q : Pattern) (ha : d268283 q = 1) (hb : d326500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268283, d326500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268283, d326500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268289 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268290 q = 1) (hb : d326501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268290, d326501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268290, d326501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268291 q = 1) (hb : d326502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268291, d326502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268291, d326502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268292 q = 1) (hb : d326503 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268292, d326503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268292, d326503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268293 q = 1) (hb : d326504 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268293, d326504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268293, d326504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104389 (p : Pattern) (ha : d268306 p = 1) (hb : d326510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268112 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268206 q = 1) (hb : d325574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268206, d325574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104385 q ha hb
    | true =>
      simp only [d268206, d325574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104386 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268219 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268220 q = 1) (hb : d325575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268220, d325575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d268220, d325575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268221 q = 1) (hb : d326491 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268221, d326491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268221, d326491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268222 q = 1) (hb : d326492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268222, d326492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268222, d326492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268226 q = 1) (hb : d326494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268226, d326494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268226, d326494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104387 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d268228 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d268229 q = 1) (hb : d326495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268229, d326495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268229, d326495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268230 q = 1) (hb : d326496 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268230, d326496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268230, d326496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d268231 q = 1) (hb : d326497 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268231, d326497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268231, d326497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d268232 q = 1) (hb : d326498 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268232, d326498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d268232, d326498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d268294 q = 1) (hb : d326505 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268294, d326505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268294, d326505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104388 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268301 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268302 q = 1) (hb : d326506 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268302, d326506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268302, d326506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268303 q = 1) (hb : d326507 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268303, d326507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268303, d326507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d268304 q = 1) (hb : d326508 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268304, d326508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d268304, d326508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d268305 q = 1) (hb : d326509 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268305, d326509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d268305, d326509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d268306 q = 1) (hb : d326510 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d268306, d326510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d268306, d326510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104390 (p : Pattern) (ha : d268312 p = 1) (hb : d326516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268307 q = 1) (hb : d326511 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d268307, d326511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268307, d326511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104389 q ha hb
  have h2 (q : Pattern) (ha : d268308 q = 1) (hb : d326512 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d268308, d326512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268308, d326512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d268309 q = 1) (hb : d326513 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d268309, d326513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268309, d326513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268310 q = 1) (hb : d326514 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d268310, d326514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268310, d326514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d268311 q = 1) (hb : d326515 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d268311, d326515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268311, d326515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268312 q = 1) (hb : d326516 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d268312, d326516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268312, d326516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104391 (p : Pattern) (ha : d268439 p = 1) (hb : d325812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268375 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268384 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d268428 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d268349 q = 1) (hb : d325807 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268349, d325807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104105 q ha hb
    | true =>
      simp only [d268349, d325807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104106 q ha hb
  have h5 (q : Pattern) (ha : d268429 q = 1) (hb : d325808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268429, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d268429, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d268435 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d268436 q = 1) (hb : d325809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268436, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d268436, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d268437 q = 1) (hb : d325810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268437, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d268437, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d268438 q = 1) (hb : d325811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268438, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268438, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d268439 q = 1) (hb : d325812 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268439, d325812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268439, d325812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104392 (p : Pattern) (ha : d268460 p = 1) (hb : d325822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268375 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268384 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268428 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268349 q = 1) (hb : d325807 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268349, d325807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104105 q ha hb
    | true =>
      simp only [d268349, d325807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104106 q ha hb
  have h4 (q : Pattern) (ha : d268429 q = 1) (hb : d325808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268429, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d268429, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d268435 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d268436 q = 1) (hb : d325809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268436, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d268436, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d268437 q = 1) (hb : d325810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268437, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268437, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268438 q = 1) (hb : d325811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268438, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268438, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d268445 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d268450 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d268452 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d268359 q = 1) (hb : d325817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268359, d325817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104108 q ha hb
    | true =>
      simp only [d268359, d325817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104109 q ha hb
  have h13 (q : Pattern) (ha : d268453 q = 1) (hb : d325818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268453, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d268453, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268456 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268457 q = 1) (hb : d325819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268457, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268457, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268458 q = 1) (hb : d325820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268458, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d268458, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d268459 q = 1) (hb : d325821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268459, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d268459, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d268460 q = 1) (hb : d325822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268460, d325822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d268460, d325822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104393 (p : Pattern) (ha : d268480 p = 1) (hb : d326520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268359 q = 1) (hb : d325817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268359, d325817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104108 q ha hb
    | true =>
      simp only [d268359, d325817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104109 q ha hb
  have h3 (q : Pattern) (ha : d268453 q = 1) (hb : d325818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268453, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268453, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268456 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268457 q = 1) (hb : d325819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268457, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268457, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268478 q = 1) (hb : d325820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268478, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268478, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268479 q = 1) (hb : d325821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268479, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268479, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268480 q = 1) (hb : d326520 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268480, d326520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268480, d326520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104394 (p : Pattern) (ha : d268565 p = 1) (hb : d326531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268554 q = 1) (hb : d326526 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268554, d326526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104145 q ha hb
    | true =>
      simp only [d268554, d326526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104148 q ha hb
  have h3 (q : Pattern) (ha : d268555 q = 1) (hb : d326527 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268555, d326527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268555, d326527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268561 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268562 q = 1) (hb : d326528 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268562, d326528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268562, d326528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268563 q = 1) (hb : d326529 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268563, d326529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268563, d326529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268564 q = 1) (hb : d326530 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268564, d326530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268564, d326530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268565 q = 1) (hb : d326531 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268565, d326531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268565, d326531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104395 (p : Pattern) (ha : d268578 p = 1) (hb : d326537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268367 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268461 q = 1) (hb : d325823 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268461, d325823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104391 q ha hb
    | true =>
      simp only [d268461, d325823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104392 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268474 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268475 q = 1) (hb : d325824 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268475, d325824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d268475, d325824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268476 q = 1) (hb : d326518 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268476, d326518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268476, d326518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268477 q = 1) (hb : d326519 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268477, d326519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268477, d326519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268481 q = 1) (hb : d326521 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268481, d326521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268481, d326521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104393 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d268483 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d268484 q = 1) (hb : d326522 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268484, d326522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268484, d326522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268485 q = 1) (hb : d326523 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268485, d326523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268485, d326523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d268486 q = 1) (hb : d326524 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268486, d326524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268486, d326524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d268487 q = 1) (hb : d326525 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268487, d326525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d268487, d326525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d268566 q = 1) (hb : d326532 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268566, d326532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268566, d326532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104394 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268573 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268574 q = 1) (hb : d326533 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268574, d326533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268574, d326533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268575 q = 1) (hb : d326534 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268575, d326534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268575, d326534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d268576 q = 1) (hb : d326535 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268576, d326535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d268576, d326535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d268577 q = 1) (hb : d326536 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268577, d326536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d268577, d326536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d268578 q = 1) (hb : d326537 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d268578, d326537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d268578, d326537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104396 (p : Pattern) (ha : d268584 p = 1) (hb : d326543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268579 q = 1) (hb : d326538 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d268579, d326538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268579, d326538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104395 q ha hb
  have h2 (q : Pattern) (ha : d268580 q = 1) (hb : d326539 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d268580, d326539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268580, d326539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d268581 q = 1) (hb : d326540 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d268581, d326540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268581, d326540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268582 q = 1) (hb : d326541 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d268582, d326541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268582, d326541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d268583 q = 1) (hb : d326542 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d268583, d326542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268583, d326542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268584 q = 1) (hb : d326543 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d268584, d326543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268584, d326543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104397 (p : Pattern) (ha : d268774 p = 1) (hb : d326140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d268754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d268669 q = 1) (hb : d326135 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268669, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104163 q ha hb
    | true =>
      simp only [d268669, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104164 q ha hb
  have h5 (q : Pattern) (ha : d268755 q = 1) (hb : d326136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268755, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d268755, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d268770 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d268771 q = 1) (hb : d326137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268771, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d268771, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d268772 q = 1) (hb : d326138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268772, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d268772, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d268773 q = 1) (hb : d326139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268773, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268773, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d268774 q = 1) (hb : d326140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268774, d326140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268774, d326140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104398 (p : Pattern) (ha : d268795 p = 1) (hb : d326150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268695 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268669 q = 1) (hb : d326135 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268669, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104163 q ha hb
    | true =>
      simp only [d268669, d326135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104164 q ha hb
  have h4 (q : Pattern) (ha : d268755 q = 1) (hb : d326136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268755, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d268755, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d268770 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d268771 q = 1) (hb : d326137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268771, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d268771, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d268772 q = 1) (hb : d326138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268772, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268772, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268773 q = 1) (hb : d326139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268773, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268773, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d268780 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d268785 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d268787 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d268679 q = 1) (hb : d326145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268679, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104166 q ha hb
    | true =>
      simp only [d268679, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104167 q ha hb
  have h13 (q : Pattern) (ha : d268788 q = 1) (hb : d326146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268788, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d268788, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268791 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268792 q = 1) (hb : d326147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268792, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268792, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268793 q = 1) (hb : d326148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268793, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d268793, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d268794 q = 1) (hb : d326149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268794, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d268794, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d268795 q = 1) (hb : d326150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268795, d326150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d268795, d326150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104399 (p : Pattern) (ha : d268815 p = 1) (hb : d326548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268787 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268679 q = 1) (hb : d326145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268679, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104166 q ha hb
    | true =>
      simp only [d268679, d326145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104167 q ha hb
  have h3 (q : Pattern) (ha : d268788 q = 1) (hb : d326146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268788, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268788, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268791 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268792 q = 1) (hb : d326147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268792, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268792, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268813 q = 1) (hb : d326148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268813, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268813, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268814 q = 1) (hb : d326149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268814, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268814, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268815 q = 1) (hb : d326548 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268815, d326548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268815, d326548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104400 (p : Pattern) (ha : d268936 p = 1) (hb : d326559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268911 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268916 q = 1) (hb : d326554 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268916, d326554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104205 q ha hb
    | true =>
      simp only [d268916, d326554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104210 q ha hb
  have h3 (q : Pattern) (ha : d268917 q = 1) (hb : d326555 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268917, d326555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268917, d326555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268932 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268933 q = 1) (hb : d326556 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268933, d326556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268933, d326556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268934 q = 1) (hb : d326557 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268934, d326557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268934, d326557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268935 q = 1) (hb : d326558 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268935, d326558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268935, d326558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268936 q = 1) (hb : d326559 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268936, d326559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268936, d326559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104401 (p : Pattern) (ha : d268949 p = 1) (hb : d326565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268796 q = 1) (hb : d326151 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268796, d326151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104397 q ha hb
    | true =>
      simp only [d268796, d326151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104398 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d268810 q = 1) (hb : d326152 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268810, d326152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d268810, d326152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268811 q = 1) (hb : d326546 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268811, d326546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268811, d326546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268812 q = 1) (hb : d326547 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268812, d326547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268812, d326547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268816 q = 1) (hb : d326549 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268816, d326549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268816, d326549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104399 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d268818 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d268819 q = 1) (hb : d326550 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268819, d326550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268819, d326550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268820 q = 1) (hb : d326551 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268820, d326551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268820, d326551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d268821 q = 1) (hb : d326552 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268821, d326552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268821, d326552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d268822 q = 1) (hb : d326553 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268822, d326553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d268822, d326553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d268937 q = 1) (hb : d326560 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268937, d326560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268937, d326560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104400 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268944 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268945 q = 1) (hb : d326561 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268945, d326561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268945, d326561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268946 q = 1) (hb : d326562 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268946, d326562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268946, d326562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d268947 q = 1) (hb : d326563 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268947, d326563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d268947, d326563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d268948 q = 1) (hb : d326564 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268948, d326564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d268948, d326564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d268949 q = 1) (hb : d326565 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d268949, d326565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d268949, d326565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104402 (p : Pattern) (ha : d268955 p = 1) (hb : d326571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268950 q = 1) (hb : d326566 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d268950, d326566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268950, d326566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104401 q ha hb
  have h2 (q : Pattern) (ha : d268951 q = 1) (hb : d326567 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d268951, d326567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268951, d326567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d268952 q = 1) (hb : d326568 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d268952, d326568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268952, d326568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268953 q = 1) (hb : d326569 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d268953, d326569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268953, d326569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d268954 q = 1) (hb : d326570 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d268954, d326570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268954, d326570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268955 q = 1) (hb : d326571 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d268955, d326571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268955, d326571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104403 (p : Pattern) (ha : d269204 p = 1) (hb : d324661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d269171 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d269086 q = 1) (hb : d324656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269086, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104227 q ha hb
    | true =>
      simp only [d269086, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104228 q ha hb
  have h5 (q : Pattern) (ha : d269172 q = 1) (hb : d324657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269172, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d269172, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d269200 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d269201 q = 1) (hb : d324658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269201, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269201, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d269202 q = 1) (hb : d324659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269202, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269202, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269203 q = 1) (hb : d324660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269203, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269203, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269204 q = 1) (hb : d324661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269204, d324661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269204, d324661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104404 (p : Pattern) (ha : d269226 p = 1) (hb : d324671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269112 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269086 q = 1) (hb : d324656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269086, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104227 q ha hb
    | true =>
      simp only [d269086, d324656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104228 q ha hb
  have h4 (q : Pattern) (ha : d269172 q = 1) (hb : d324657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269172, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269172, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d269200 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d269201 q = 1) (hb : d324658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269201, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269201, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d269202 q = 1) (hb : d324659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269202, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269202, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269203 q = 1) (hb : d324660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269203, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269203, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269210 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d269215 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d269218 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d269096 q = 1) (hb : d324666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269096, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104230 q ha hb
    | true =>
      simp only [d269096, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104231 q ha hb
  have h13 (q : Pattern) (ha : d269219 q = 1) (hb : d324667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269219, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d269219, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269222 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269223 q = 1) (hb : d324668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269223, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269223, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269224 q = 1) (hb : d324669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269224, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269224, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269225 q = 1) (hb : d324670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269225, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d269225, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269226 q = 1) (hb : d324671 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269226, d324671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269226, d324671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104405 (p : Pattern) (ha : d269251 p = 1) (hb : d325181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269218 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269096 q = 1) (hb : d324666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269096, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104230 q ha hb
    | true =>
      simp only [d269096, d324666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104231 q ha hb
  have h3 (q : Pattern) (ha : d269219 q = 1) (hb : d324667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269219, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269219, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269222 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269223 q = 1) (hb : d324668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269223, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269223, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269249 q = 1) (hb : d324669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269249, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269249, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269250 q = 1) (hb : d324670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269250, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269250, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269251 q = 1) (hb : d325181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269251, d325181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269251, d325181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104406 (p : Pattern) (ha : d269360 p = 1) (hb : d324813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269313 q = 1) (hb : d324798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269313, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104264 q ha hb
    | true =>
      simp only [d269313, d324798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104266 q ha hb
  have h2 (q : Pattern) (ha : d269314 q = 1) (hb : d324799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269314, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269314, d324799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269315 q = 1) (hb : d324800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269315, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269315, d324800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269327 q = 1) (hb : d324803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269327, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104266 q ha hb
    | true =>
      simp only [d269327, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104267 q ha hb
  have h5 (q : Pattern) (ha : d269328 q = 1) (hb : d324804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269328, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269328, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269329 q = 1) (hb : d324805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269329, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269329, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269330 q = 1) (hb : d324806 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269330, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269330, d324806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269346 q = 1) (hb : d324803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269346, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104266 q ha hb
    | true =>
      simp only [d269346, d324803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104271 q ha hb
  have h9 (q : Pattern) (ha : d269347 q = 1) (hb : d324804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269347, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269347, d324804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269348 q = 1) (hb : d324805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269348, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269348, d324805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269349 q = 1) (hb : d324811 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269349, d324811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269349, d324811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269359 q = 1) (hb : d324812 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269359, d324812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269359, d324812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269360 q = 1) (hb : d324813 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269360, d324813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269360, d324813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro104407 (p : Pattern) (ha : d269366 p = 1) (hb : d324827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269361 q = 1) (hb : d324814 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269361, d324814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104406 q ha hb
    | true =>
      simp only [d269361, d324814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269362 q = 1) (hb : d324815 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269362, d324815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269362, d324815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269352 q = 1) (hb : d324822 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269352, d324822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104272 q ha hb
    | true =>
      simp only [d269352, d324822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269353 q = 1) (hb : d324823 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269353, d324823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269353, d324823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269363 q = 1) (hb : d324824 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269363, d324824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269363, d324824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269364 q = 1) (hb : d324825 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269364, d324825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269364, d324825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269365 q = 1) (hb : d324826 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269365, d324826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269365, d324826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269366 q = 1) (hb : d324827 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269366, d324827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269366, d324827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104408 (p : Pattern) (ha : d269402 p = 1) (hb : d325192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269358 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269371 q = 1) (hb : d325187 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269371, d325187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104407 q ha hb
    | true =>
      simp only [d269371, d325187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104279 q ha hb
  have h3 (q : Pattern) (ha : d269372 q = 1) (hb : d325188 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269372, d325188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269372, d325188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269398 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269399 q = 1) (hb : d325189 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269399, d325189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269399, d325189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269400 q = 1) (hb : d325190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269400, d325190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269400, d325190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269401 q = 1) (hb : d325191 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269401, d325191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269401, d325191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269402 q = 1) (hb : d325192 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269402, d325192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269402, d325192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104409 (p : Pattern) (ha : d269415 p = 1) (hb : d325198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269104 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269227 q = 1) (hb : d324672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269227, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104403 q ha hb
    | true =>
      simp only [d269227, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104404 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269246 q = 1) (hb : d324673 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269246, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269246, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269247 q = 1) (hb : d325179 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269247, d325179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269247, d325179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269248 q = 1) (hb : d325180 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269248, d325180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269248, d325180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269252 q = 1) (hb : d325182 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269252, d325182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269252, d325182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104405 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d269254 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d269255 q = 1) (hb : d325183 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269255, d325183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269255, d325183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d269256 q = 1) (hb : d325184 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269256, d325184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269256, d325184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d269257 q = 1) (hb : d325185 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269257, d325185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269257, d325185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d269258 q = 1) (hb : d325186 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269258, d325186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269258, d325186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269403 q = 1) (hb : d325193 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269403, d325193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269403, d325193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104408 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269410 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269411 q = 1) (hb : d325194 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269411, d325194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269411, d325194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269412 q = 1) (hb : d325195 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269412, d325195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269412, d325195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d269413 q = 1) (hb : d325196 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269413, d325196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269413, d325196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d269414 q = 1) (hb : d325197 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269414, d325197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269414, d325197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d269415 q = 1) (hb : d325198 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269415, d325198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269415, d325198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104410 (p : Pattern) (ha : d269421 p = 1) (hb : d325204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269416 q = 1) (hb : d325199 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269416, d325199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269416, d325199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104409 q ha hb
  have h2 (q : Pattern) (ha : d269417 q = 1) (hb : d325200 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269417, d325200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269417, d325200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269418 q = 1) (hb : d325201 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269418, d325201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269418, d325201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269419 q = 1) (hb : d325202 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269419, d325202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269419, d325202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269420 q = 1) (hb : d325203 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269420, d325203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269420, d325203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269421 q = 1) (hb : d325204 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269421, d325204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269421, d325204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104411 (p : Pattern) (ha : d46921 p = 1) (hb : d269633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269563 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269572 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d269600 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46916 q = 1) (hb : d269537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, d269537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104294 q ha hb
    | true =>
      simp only [d46916, d269537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104295 q ha hb
  have h5 (q : Pattern) (ha : d46917 q = 1) (hb : d269601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d269601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46917, d269601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d269629 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46918 q = 1) (hb : d269630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d269630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46918, d269630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46919 q = 1) (hb : d269631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d269631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46919, d269631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46920 q = 1) (hb : d269632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d269632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46920, d269632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46921 q = 1) (hb : d269633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46921, d269633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46921, d269633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104412 (p : Pattern) (ha : d46931 p = 1) (hb : d269655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46916 q = 1) (hb : d269537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, d269537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104294 q ha hb
    | true =>
      simp only [d46916, d269537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104295 q ha hb
  have h4 (q : Pattern) (ha : d46917 q = 1) (hb : d269601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d269601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46917, d269601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d269629 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46918 q = 1) (hb : d269630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d269630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46918, d269630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46919 q = 1) (hb : d269631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d269631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46919, d269631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46920 q = 1) (hb : d269632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d269632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46920, d269632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269639 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d269644 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d269647 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d46926 q = 1) (hb : d269547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, d269547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104297 q ha hb
    | true =>
      simp only [d46926, d269547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104298 q ha hb
  have h13 (q : Pattern) (ha : d46927 q = 1) (hb : d269648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d269648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46927, d269648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46928 q = 1) (hb : d269652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d269652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46928, d269652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46929 q = 1) (hb : d269653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d269653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46929, d269653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46930 q = 1) (hb : d269654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d269654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46930, d269654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46931 q = 1) (hb : d269655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46931, d269655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46931, d269655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104413 (p : Pattern) (ha : d269680 p = 1) (hb : d321910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269647 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46926 q = 1) (hb : d269547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, d269547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104297 q ha hb
    | true =>
      simp only [d46926, d269547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104298 q ha hb
  have h3 (q : Pattern) (ha : d46927 q = 1) (hb : d269648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d269648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46927, d269648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269651 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46928 q = 1) (hb : d269652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d269652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46928, d269652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46929 q = 1) (hb : d269678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d269678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46929, d269678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46930 q = 1) (hb : d269679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d269679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46930, d269679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269680 q = 1) (hb : d321910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269680, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269680, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro104414 (p : Pattern) (ha : d47117 p = 1) (hb : d269775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47097 q = 1) (hb : d269728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, d269728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104330 q ha hb
    | true =>
      simp only [d47097, d269728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104305 q ha hb
  have h2 (q : Pattern) (ha : d47098 q = 1) (hb : d269729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, d269729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47098, d269729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47099 q = 1) (hb : d269730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, d269730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47099, d269730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d47107 q = 1) (hb : d269742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d269742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104305 q ha hb
    | true =>
      simp only [d47107, d269742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104332 q ha hb
  have h5 (q : Pattern) (ha : d47108 q = 1) (hb : d269743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d269743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47108, d269743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47109 q = 1) (hb : d269744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d269744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47109, d269744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47110 q = 1) (hb : d269745 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, d269745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47110, d269745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47107 q = 1) (hb : d269761 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d269761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104305 q ha hb
    | true =>
      simp only [d47107, d269761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104306 q ha hb
  have h9 (q : Pattern) (ha : d47108 q = 1) (hb : d269762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d269762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47108, d269762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d47109 q = 1) (hb : d269763 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d269763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47109, d269763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d47115 q = 1) (hb : d269764 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47115, d269764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d47115, d269764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d47116 q = 1) (hb : d269774 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47116, d269774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47116, d269774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d47117 q = 1) (hb : d269775 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47117, d269775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d47117, d269775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro104415 (p : Pattern) (ha : d47131 p = 1) (hb : d269781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47118 q = 1) (hb : d269776 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47118, d269776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104414 q ha hb
    | true =>
      simp only [d47118, d269776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47119 q = 1) (hb : d269777 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47119, d269777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47119, d269777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47126 q = 1) (hb : d269767 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47126, d269767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104307 q ha hb
    | true =>
      simp only [d47126, d269767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47127 q = 1) (hb : d269768 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47127, d269768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47127, d269768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47128 q = 1) (hb : d269778 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47128, d269778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47128, d269778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47129 q = 1) (hb : d269779 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47129, d269779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47129, d269779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47130 q = 1) (hb : d269780 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47130, d269780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47130, d269780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47131 q = 1) (hb : d269781 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47131, d269781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47131, d269781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104416 (p : Pattern) (ha : d269789 p = 1) (hb : d326581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269784 q = 1) (hb : d326576 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d269784, d326576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88960 q ha hb
    | true =>
      simp only [d269784, d326576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104283 q hb ha
  have h2 (q : Pattern) (ha : d269785 q = 1) (hb : d326577 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d269785, d326577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269785, d326577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d269786 q = 1) (hb : d326578 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269786, d326578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269786, d326578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46871 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104283 q ha hb
    | true =>
      simp only [d46871, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d46872 q = 1) (hb : d269459 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46872, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46873 q = 1) (hb : d269460 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46873, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d269787 q = 1) (hb : d326579 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269787, d326579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269787, d326579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d269788 q = 1) (hb : d326580 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269788, d326580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269788, d326580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d269789 q = 1) (hb : d326581 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269789, d326581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269789, d326581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h11 p ha hb
theorem andIntro104417 (p : Pattern) (ha : d269795 p = 1) (hb : d326587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47086 q = 1) (hb : d269722 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d269722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47086, d269722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104286 q ha hb
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d269482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104286 q ha hb
    | true =>
      simp only [d46877, d269482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47087 q = 1) (hb : d269723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d269723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, d269723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46878 q = 1) (hb : d269483 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d269483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47088 q = 1) (hb : d269724 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d269724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, d269724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47089 q = 1) (hb : d269725 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d269725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, d269725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47095 q = 1) (hb : d269759 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, d269759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, d269759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47101 q = 1) (hb : d269736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, d269736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47101, d269736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104289 q ha hb
  have h9 (q : Pattern) (ha : d46889 q = 1) (hb : d269505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, d269505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104289 q ha hb
    | true =>
      simp only [d46889, d269505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d47102 q = 1) (hb : d269737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, d269737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47102, d269737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269790 q = 1) (hb : d326582 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269790, d326582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104416 q ha hb
    | true =>
      simp only [d269790, d326582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269791 q = 1) (hb : d326583 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269791, d326583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269791, d326583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269792 q = 1) (hb : d326584 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269792, d326584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269792, d326584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269793 q = 1) (hb : d326585 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269793, d326585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269793, d326585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269794 q = 1) (hb : d326586 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269794, d326586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269794, d326586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269795 q = 1) (hb : d326587 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269795, d326587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d269795, d326587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro104418 (p : Pattern) (ha : d269801 p = 1) (hb : d326593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269796 q = 1) (hb : d326588 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269796, d326588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104305 q hb ha
    | true =>
      simp only [d269796, d326588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104417 q ha hb
  have h2 (q : Pattern) (ha : d269797 q = 1) (hb : d326589 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269797, d326589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269797, d326589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269798 q = 1) (hb : d326590 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269798, d326590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269798, d326590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269799 q = 1) (hb : d326591 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269799, d326591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269799, d326591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269800 q = 1) (hb : d326592 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269800, d326592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269800, d326592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269801 q = 1) (hb : d326593 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269801, d326593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269801, d326593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104419 (p : Pattern) (ha : d269807 p = 1) (hb : d326599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269802 q = 1) (hb : d326594 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269802, d326594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104418 q ha hb
    | true =>
      simp only [d269802, d326594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269803 q = 1) (hb : d326595 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269803, d326595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269803, d326595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269804 q = 1) (hb : d326596 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269804, d326596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269804, d326596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269805 q = 1) (hb : d326597 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269805, d326597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269805, d326597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269806 q = 1) (hb : d326598 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269806, d326598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269806, d326598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269807 q = 1) (hb : d326599 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269807, d326599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269807, d326599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104420 (p : Pattern) (ha : d269839 p = 1) (hb : d326605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269808 q = 1) (hb : d326600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269808, d326600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104415 q hb ha
    | true =>
      simp only [d269808, d326600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104419 q ha hb
  have h3 (q : Pattern) (ha : d269809 q = 1) (hb : d326601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269809, d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269809, d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269835 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269836 q = 1) (hb : d326602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269836, d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269836, d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269837 q = 1) (hb : d326603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269837, d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269837, d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269838 q = 1) (hb : d326604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269838, d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269838, d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269839 q = 1) (hb : d326605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269839, d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269839, d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104421 (p : Pattern) (ha : d269856 p = 1) (hb : d326611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269555 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46932 q = 1) (hb : d269656 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, d269656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104411 q ha hb
    | true =>
      simp only [d46932, d269656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104412 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269674 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46933 q = 1) (hb : d269675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, d269675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46933, d269675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269676 q = 1) (hb : d321908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269676, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d269676, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269677 q = 1) (hb : d321909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269677, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269677, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269681 q = 1) (hb : d321911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269681, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269681, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104413 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d269683 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d269684 q = 1) (hb : d321912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269684, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269684, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d269685 q = 1) (hb : d321913 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269685, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269685, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d269686 q = 1) (hb : d321914 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269686, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269686, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d269687 q = 1) (hb : d321915 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269687, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269687, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269840 q = 1) (hb : d326606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269840, d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269840, d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104420 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269851 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269852 q = 1) (hb : d326607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269852, d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269852, d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269853 q = 1) (hb : d326608 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269853, d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269853, d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d269854 q = 1) (hb : d326609 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269854, d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269854, d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d269855 q = 1) (hb : d326610 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269855, d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269855, d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d269856 q = 1) (hb : d326611 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269856, d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269856, d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104422 (p : Pattern) (ha : d269862 p = 1) (hb : d326617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269857 q = 1) (hb : d326612 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269857, d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269857, d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104421 q ha hb
  have h2 (q : Pattern) (ha : d269858 q = 1) (hb : d326613 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269858, d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269858, d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269859 q = 1) (hb : d326614 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269859, d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269859, d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269860 q = 1) (hb : d326615 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269860, d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269860, d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269861 q = 1) (hb : d326616 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269861, d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269861, d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269862 q = 1) (hb : d326617 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269862, d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269862, d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104423 (p : Pattern) (ha : d269868 p = 1) (hb : d326623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d268313 q = 1) (hb : d326517 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268313, d326517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104384 q ha hb
    | true =>
      simp only [d268313, d326517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104390 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268585 q = 1) (hb : d326544 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268585, d326544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268585, d326544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104396 q ha hb
  have h3 (q : Pattern) (ha : d268586 q = 1) (hb : d326545 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d268586, d326545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d268586, d326545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268956 q = 1) (hb : d326572 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268956, d326572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268956, d326572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104402 q ha hb
  have h5 (q : Pattern) (ha : d268957 q = 1) (hb : d326573 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d268957, d326573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268957, d326573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268958 q = 1) (hb : d326574 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d268958, d326574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268958, d326574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269422 q = 1) (hb : d325205 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d269422, d325205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269422, d325205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104410 q ha hb
  have h8 (q : Pattern) (ha : d269423 q = 1) (hb : d325206 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d269423, d325206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269423, d325206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269424 q = 1) (hb : d325207 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d269424, d325207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269424, d325207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269425 q = 1) (hb : d326575 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d269425, d326575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269425, d326575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269863 q = 1) (hb : d326618 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d269863, d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269863, d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104422 q ha hb
  have h12 (q : Pattern) (ha : d269864 q = 1) (hb : d326619 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d269864, d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269864, d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269865 q = 1) (hb : d326620 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d269865, d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269865, d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269866 q = 1) (hb : d326621 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d269866, d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269866, d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269867 q = 1) (hb : d326622 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d269867, d326622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269867, d326622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269868 q = 1) (hb : d326623 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d269868, d326623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269868, d326623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro104424 (p : Pattern) (ha : d269874 p = 1) (hb : d326629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269869 q = 1) (hb : d326624 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d269869, d326624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104423 q ha hb
    | true =>
      simp only [d269869, d326624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269870 q = 1) (hb : d326625 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d269870, d326625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269870, d326625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269871 q = 1) (hb : d326626 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d269871, d326626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269871, d326626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269872 q = 1) (hb : d326627 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d269872, d326627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269872, d326627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269873 q = 1) (hb : d326628 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d269873, d326628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269873, d326628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269874 q = 1) (hb : d326629 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d269874, d326629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269874, d326629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104425 (p : Pattern) (ha : d269880 p = 1) (hb : d326635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269875 q = 1) (hb : d326630 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d269875, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104424 q ha hb
    | true =>
      simp only [d269875, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269876 q = 1) (hb : d326631 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d269876, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269876, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269877 q = 1) (hb : d326632 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d269877, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269877, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269878 q = 1) (hb : d326633 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d269878, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269878, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269879 q = 1) (hb : d326634 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d269879, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269879, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269880 q = 1) (hb : d326635 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d269880, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269880, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104426 (p : Pattern) (ha : d269886 p = 1) (hb : d326641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269881 q = 1) (hb : d326636 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d269881, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104425 q ha hb
    | true =>
      simp only [d269881, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269882 q = 1) (hb : d326637 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d269882, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269882, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269883 q = 1) (hb : d326638 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d269883, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269883, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269884 q = 1) (hb : d326639 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d269884, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269884, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269885 q = 1) (hb : d326640 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d269885, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269885, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269886 q = 1) (hb : d326641 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d269886, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269886, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104427 (p : Pattern) (ha : d269892 p = 1) (hb : d326647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269887 q = 1) (hb : d326642 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d269887, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104426 q ha hb
    | true =>
      simp only [d269887, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269888 q = 1) (hb : d326643 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d269888, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269888, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269889 q = 1) (hb : d326644 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d269889, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269889, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269890 q = 1) (hb : d326645 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d269890, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269890, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269891 q = 1) (hb : d326646 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d269891, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269891, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269892 q = 1) (hb : d326647 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d269892, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269892, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104428 (p : Pattern) (ha : d269898 p = 1) (hb : d326653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269893 q = 1) (hb : d326648 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d269893, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104427 q ha hb
    | true =>
      simp only [d269893, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269894 q = 1) (hb : d326649 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d269894, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269894, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269895 q = 1) (hb : d326650 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d269895, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269895, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269896 q = 1) (hb : d326651 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d269896, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269896, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269897 q = 1) (hb : d326652 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d269897, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269897, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269898 q = 1) (hb : d326653 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d269898, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269898, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104429 (p : Pattern) (ha : d269904 p = 1) (hb : d326659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269899 q = 1) (hb : d326654 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d269899, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104428 q ha hb
    | true =>
      simp only [d269899, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269900 q = 1) (hb : d326655 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d269900, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269900, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269901 q = 1) (hb : d326656 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d269901, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269901, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269902 q = 1) (hb : d326657 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d269902, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269902, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269903 q = 1) (hb : d326658 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d269903, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269903, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269904 q = 1) (hb : d326659 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d269904, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269904, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104430 (p : Pattern) (ha : d269910 p = 1) (hb : d326665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269905 q = 1) (hb : d326660 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d269905, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104429 q ha hb
    | true =>
      simp only [d269905, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269906 q = 1) (hb : d326661 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d269906, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269906, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269907 q = 1) (hb : d326662 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d269907, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269907, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269908 q = 1) (hb : d326663 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d269908, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269908, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269909 q = 1) (hb : d326664 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d269909, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269909, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269910 q = 1) (hb : d326665 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d269910, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269910, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104431 (p : Pattern) (ha : d269953 p = 1) (hb : d325396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36106 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36112 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d325332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269949 q = 1) (hb : d325392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269949, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d269949, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d36174 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d269950 q = 1) (hb : d325393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269950, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269950, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d269951 q = 1) (hb : d325394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269951, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269951, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269952 q = 1) (hb : d325395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269952, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269952, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269953 q = 1) (hb : d325396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269953, d325396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269953, d325396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104432 (p : Pattern) (ha : d269958 p = 1) (hb : d325403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36106 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36145 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d325332 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d269949 q = 1) (hb : d325392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269949, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269949, d325392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d36174 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d269950 q = 1) (hb : d325393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269950, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269950, d325393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d269951 q = 1) (hb : d325394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269951, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269951, d325394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269952 q = 1) (hb : d325395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269952, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269952, d325395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d36183 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d36187 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d36189 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d325339 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d269954 q = 1) (hb : d325399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269954, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d269954, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36195 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269955 q = 1) (hb : d325400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269955, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269955, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269956 q = 1) (hb : d325401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269956, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269956, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269957 q = 1) (hb : d325402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269957, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d269957, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269958 q = 1) (hb : d325403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269958, d325403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269958, d325403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104433 (p : Pattern) (ha : d269965 p = 1) (hb : d326468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d325339 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269954 q = 1) (hb : d325399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269954, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269954, d325399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36195 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269955 q = 1) (hb : d325400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269955, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269955, d325400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269963 q = 1) (hb : d325401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269963, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269963, d325401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269964 q = 1) (hb : d325402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269964, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269964, d325402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269965 q = 1) (hb : d326468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269965, d326468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269965, d326468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104434 (p : Pattern) (ha : d269975 p = 1) (hb : d326478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36237 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d325375 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269971 q = 1) (hb : d326474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269971, d326474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269971, d326474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36263 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269972 q = 1) (hb : d326475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269972, d326475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269972, d326475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269973 q = 1) (hb : d326476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269973, d326476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269973, d326476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269974 q = 1) (hb : d326477 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269974, d326477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269974, d326477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269975 q = 1) (hb : d326478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269975, d326478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269975, d326478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104435 (p : Pattern) (ha : d269981 p = 1) (hb : d326484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269959 q = 1) (hb : d325404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269959, d325404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104431 q ha hb
    | true =>
      simp only [d269959, d325404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104432 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36202 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269960 q = 1) (hb : d325405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269960, d325405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269960, d325405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269961 q = 1) (hb : d326466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269961, d326466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269961, d326466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269962 q = 1) (hb : d326467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269962, d326467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269962, d326467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269966 q = 1) (hb : d326469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269966, d326469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269966, d326469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104433 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d269967 q = 1) (hb : d326470 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269967, d326470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269967, d326470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d269968 q = 1) (hb : d326471 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269968, d326471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269968, d326471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d269969 q = 1) (hb : d326472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269969, d326472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269969, d326472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d269970 q = 1) (hb : d326473 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269970, d326473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269970, d326473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269976 q = 1) (hb : d326479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269976, d326479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269976, d326479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104434 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269977 q = 1) (hb : d326480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269977, d326480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269977, d326480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269978 q = 1) (hb : d326481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269978, d326481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269978, d326481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d269979 q = 1) (hb : d326482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269979, d326482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269979, d326482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d269980 q = 1) (hb : d326483 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269980, d326483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269980, d326483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d269981 q = 1) (hb : d326484 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269981, d326484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269981, d326484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104436 (p : Pattern) (ha : d269987 p = 1) (hb : d326490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d269944 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d269944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d269944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68689 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d269945 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d269945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d269945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d269946 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d269946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d269946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d269947 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d269947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d269947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d269948 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d269948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d269948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269982 q = 1) (hb : d326485 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269982, d326485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269982, d326485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104435 q ha hb
  have h8 (q : Pattern) (ha : d269983 q = 1) (hb : d326486 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269983, d326486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269983, d326486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269984 q = 1) (hb : d326487 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269984, d326487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269984, d326487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269985 q = 1) (hb : d326488 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269985, d326488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269985, d326488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269986 q = 1) (hb : d326489 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269986, d326489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269986, d326489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269987 q = 1) (hb : d326490 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269987, d326490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d269987, d326490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro104437 (p : Pattern) (ha : d269992 p = 1) (hb : d325563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36323 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36332 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36376 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d325558 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269988 q = 1) (hb : d325559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269988, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d269988, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d36425 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d269989 q = 1) (hb : d325560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269989, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269989, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d269990 q = 1) (hb : d325561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269990, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269990, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269991 q = 1) (hb : d325562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269991, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269991, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269992 q = 1) (hb : d325563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269992, d325563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269992, d325563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104438 (p : Pattern) (ha : d269997 p = 1) (hb : d325573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36323 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36332 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36376 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d325558 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d269988 q = 1) (hb : d325559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269988, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269988, d325559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d36425 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d269989 q = 1) (hb : d325560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269989, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269989, d325560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d269990 q = 1) (hb : d325561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269990, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269990, d325561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269991 q = 1) (hb : d325562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269991, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269991, d325562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d36435 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d36440 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d36442 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d325568 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d269993 q = 1) (hb : d325569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269993, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d269993, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36449 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269994 q = 1) (hb : d325570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269994, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269994, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269995 q = 1) (hb : d325571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269995, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269995, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269996 q = 1) (hb : d325572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269996, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d269996, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269997 q = 1) (hb : d325573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269997, d325573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269997, d325573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104439 (p : Pattern) (ha : d270004 p = 1) (hb : d326493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36442 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d325568 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269993 q = 1) (hb : d325569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269993, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269993, d325569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36449 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269994 q = 1) (hb : d325570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269994, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269994, d325570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270002 q = 1) (hb : d325571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270002, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270002, d325571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270003 q = 1) (hb : d325572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270003, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270003, d325572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270004 q = 1) (hb : d326493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270004, d326493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270004, d326493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104440 (p : Pattern) (ha : d270014 p = 1) (hb : d326504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36525 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d326499 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270010 q = 1) (hb : d326500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270010, d326500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270010, d326500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36565 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270011 q = 1) (hb : d326501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270011, d326501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270011, d326501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270012 q = 1) (hb : d326502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270012, d326502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270012, d326502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270013 q = 1) (hb : d326503 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270013, d326503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270013, d326503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270014 q = 1) (hb : d326504 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270014, d326504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270014, d326504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104441 (p : Pattern) (ha : d270020 p = 1) (hb : d326510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269998 q = 1) (hb : d325574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269998, d325574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104437 q ha hb
    | true =>
      simp only [d269998, d325574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104438 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36467 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269999 q = 1) (hb : d325575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269999, d325575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269999, d325575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270000 q = 1) (hb : d326491 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270000, d326491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270000, d326491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270001 q = 1) (hb : d326492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270001, d326492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270001, d326492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270005 q = 1) (hb : d326494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270005, d326494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270005, d326494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104439 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d36476 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d270006 q = 1) (hb : d326495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270006, d326495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270006, d326495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d270007 q = 1) (hb : d326496 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270007, d326496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270007, d326496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d270008 q = 1) (hb : d326497 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270008, d326497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270008, d326497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d270009 q = 1) (hb : d326498 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270009, d326498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270009, d326498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d270015 q = 1) (hb : d326505 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270015, d326505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270015, d326505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104440 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36581 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270016 q = 1) (hb : d326506 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270016, d326506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270016, d326506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270017 q = 1) (hb : d326507 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270017, d326507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d270017, d326507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d270018 q = 1) (hb : d326508 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270018, d326508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d270018, d326508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d270019 q = 1) (hb : d326509 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270019, d326509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d270019, d326509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d270020 q = 1) (hb : d326510 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270020, d326510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270020, d326510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104442 (p : Pattern) (ha : d270026 p = 1) (hb : d326516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270021 q = 1) (hb : d326511 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270021, d326511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270021, d326511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104441 q ha hb
  have h2 (q : Pattern) (ha : d270022 q = 1) (hb : d326512 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270022, d326512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270022, d326512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270023 q = 1) (hb : d326513 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270023, d326513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270023, d326513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270024 q = 1) (hb : d326514 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270024, d326514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270024, d326514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270025 q = 1) (hb : d326515 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270025, d326515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270025, d326515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270026 q = 1) (hb : d326516 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270026, d326516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270026, d326516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104443 (p : Pattern) (ha : d270032 p = 1) (hb : d325812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36655 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36708 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d325807 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270028 q = 1) (hb : d325808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270028, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d270028, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d36776 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d270029 q = 1) (hb : d325809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270029, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270029, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d270030 q = 1) (hb : d325810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270030, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d270030, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d270031 q = 1) (hb : d325811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270031, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270031, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270032 q = 1) (hb : d325812 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270032, d325812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270032, d325812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104444 (p : Pattern) (ha : d270037 p = 1) (hb : d325822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36655 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36664 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36708 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d325807 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d270028 q = 1) (hb : d325808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270028, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d270028, d325808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d36776 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d270029 q = 1) (hb : d325809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270029, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270029, d325809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d270030 q = 1) (hb : d325810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270030, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270030, d325810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270031 q = 1) (hb : d325811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270031, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270031, d325811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d36786 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d36791 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d36793 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d325817 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d270033 q = 1) (hb : d325818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270033, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d270033, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36800 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270034 q = 1) (hb : d325819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270034, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270034, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270035 q = 1) (hb : d325820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270035, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d270035, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d270036 q = 1) (hb : d325821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270036, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d270036, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d270037 q = 1) (hb : d325822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270037, d325822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d270037, d325822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104445 (p : Pattern) (ha : d270044 p = 1) (hb : d326520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36793 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d325817 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270033 q = 1) (hb : d325818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270033, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270033, d325818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36800 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270034 q = 1) (hb : d325819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270034, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270034, d325819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270042 q = 1) (hb : d325820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270042, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270042, d325820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270043 q = 1) (hb : d325821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270043, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270043, d325821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270044 q = 1) (hb : d326520 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270044, d326520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270044, d326520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104446 (p : Pattern) (ha : d270054 p = 1) (hb : d326531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36893 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d326526 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270050 q = 1) (hb : d326527 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270050, d326527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270050, d326527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36948 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270051 q = 1) (hb : d326528 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270051, d326528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270051, d326528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270052 q = 1) (hb : d326529 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270052, d326529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270052, d326529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270053 q = 1) (hb : d326530 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270053, d326530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270053, d326530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270054 q = 1) (hb : d326531 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270054, d326531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270054, d326531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104447 (p : Pattern) (ha : d270060 p = 1) (hb : d326537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36647 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270038 q = 1) (hb : d325823 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270038, d325823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104443 q ha hb
    | true =>
      simp only [d270038, d325823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104444 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270039 q = 1) (hb : d325824 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270039, d325824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270039, d325824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270040 q = 1) (hb : d326518 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270040, d326518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270040, d326518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270041 q = 1) (hb : d326519 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270041, d326519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270041, d326519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270045 q = 1) (hb : d326521 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270045, d326521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270045, d326521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104445 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d36827 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d270046 q = 1) (hb : d326522 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270046, d326522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270046, d326522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d270047 q = 1) (hb : d326523 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270047, d326523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270047, d326523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d270048 q = 1) (hb : d326524 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270048, d326524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270048, d326524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d270049 q = 1) (hb : d326525 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270049, d326525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270049, d326525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d270055 q = 1) (hb : d326532 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270055, d326532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270055, d326532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104446 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36964 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270056 q = 1) (hb : d326533 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270056, d326533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270056, d326533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270057 q = 1) (hb : d326534 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270057, d326534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d270057, d326534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d270058 q = 1) (hb : d326535 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270058, d326535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d270058, d326535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d270059 q = 1) (hb : d326536 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270059, d326536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d270059, d326536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d270060 q = 1) (hb : d326537 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270060, d326537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270060, d326537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104448 (p : Pattern) (ha : d270066 p = 1) (hb : d326543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270061 q = 1) (hb : d326538 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270061, d326538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270061, d326538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104447 q ha hb
  have h2 (q : Pattern) (ha : d270062 q = 1) (hb : d326539 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270062, d326539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270062, d326539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270063 q = 1) (hb : d326540 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270063, d326540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270063, d326540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270064 q = 1) (hb : d326541 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270064, d326541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270064, d326541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270065 q = 1) (hb : d326542 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270065, d326542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270065, d326542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270066 q = 1) (hb : d326543 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270066, d326543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270066, d326543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104449 (p : Pattern) (ha : d270073 p = 1) (hb : d326140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d37145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d326135 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270069 q = 1) (hb : d326136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270069, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d270069, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d37247 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d270070 q = 1) (hb : d326137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270070, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270070, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d270071 q = 1) (hb : d326138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270071, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d270071, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d270072 q = 1) (hb : d326139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270072, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270072, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270073 q = 1) (hb : d326140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270073, d326140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270073, d326140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104450 (p : Pattern) (ha : d270078 p = 1) (hb : d326150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d37086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37145 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d326135 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d270069 q = 1) (hb : d326136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270069, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d270069, d326136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d37247 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d270070 q = 1) (hb : d326137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270070, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270070, d326137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d270071 q = 1) (hb : d326138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270071, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270071, d326138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270072 q = 1) (hb : d326139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270072, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270072, d326139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d37257 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d37262 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d37264 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d326145 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d270074 q = 1) (hb : d326146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270074, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d270074, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d37271 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270075 q = 1) (hb : d326147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270075, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270075, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270076 q = 1) (hb : d326148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270076, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d270076, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d270077 q = 1) (hb : d326149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270077, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d270077, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d270078 q = 1) (hb : d326150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270078, d326150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d270078, d326150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104451 (p : Pattern) (ha : d270085 p = 1) (hb : d326548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37264 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d326145 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270074 q = 1) (hb : d326146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270074, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270074, d326146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d37271 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270075 q = 1) (hb : d326147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270075, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270075, d326147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270083 q = 1) (hb : d326148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270083, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270083, d326148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270084 q = 1) (hb : d326149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270084, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270084, d326149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270085 q = 1) (hb : d326548 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270085, d326548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270085, d326548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104452 (p : Pattern) (ha : d270095 p = 1) (hb : d326559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37391 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d326554 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270091 q = 1) (hb : d326555 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270091, d326555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270091, d326555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d37464 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270092 q = 1) (hb : d326556 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270092, d326556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270092, d326556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270093 q = 1) (hb : d326557 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270093, d326557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270093, d326557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270094 q = 1) (hb : d326558 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270094, d326558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270094, d326558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270095 q = 1) (hb : d326559 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270095, d326559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270095, d326559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104453 (p : Pattern) (ha : d270101 p = 1) (hb : d326565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d37078 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270079 q = 1) (hb : d326151 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270079, d326151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104449 q ha hb
    | true =>
      simp only [d270079, d326151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104450 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270080 q = 1) (hb : d326152 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270080, d326152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270080, d326152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270081 q = 1) (hb : d326546 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270081, d326546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270081, d326546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270082 q = 1) (hb : d326547 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270082, d326547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270082, d326547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270086 q = 1) (hb : d326549 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270086, d326549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270086, d326549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104451 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d37298 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d270087 q = 1) (hb : d326550 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270087, d326550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270087, d326550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d270088 q = 1) (hb : d326551 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270088, d326551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270088, d326551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d270089 q = 1) (hb : d326552 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270089, d326552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270089, d326552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d270090 q = 1) (hb : d326553 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270090, d326553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270090, d326553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d270096 q = 1) (hb : d326560 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270096, d326560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270096, d326560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104452 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d37480 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270097 q = 1) (hb : d326561 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270097, d326561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270097, d326561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270098 q = 1) (hb : d326562 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270098, d326562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d270098, d326562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d270099 q = 1) (hb : d326563 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270099, d326563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d270099, d326563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d270100 q = 1) (hb : d326564 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270100, d326564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d270100, d326564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d270101 q = 1) (hb : d326565 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270101, d326565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270101, d326565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104454 (p : Pattern) (ha : d270107 p = 1) (hb : d326571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270102 q = 1) (hb : d326566 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270102, d326566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270102, d326566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104453 q ha hb
  have h2 (q : Pattern) (ha : d270103 q = 1) (hb : d326567 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270103, d326567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270103, d326567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270104 q = 1) (hb : d326568 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270104, d326568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270104, d326568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270105 q = 1) (hb : d326569 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270105, d326569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270105, d326569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270106 q = 1) (hb : d326570 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270106, d326570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270106, d326570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270107 q = 1) (hb : d326571 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270107, d326571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270107, d326571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104455 (p : Pattern) (ha : d271084 p = 1) (hb : d324661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37657 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d37707 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d324656 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271080 q = 1) (hb : d324657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271080, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d271080, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d37864 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d271081 q = 1) (hb : d324658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271081, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271081, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d271082 q = 1) (hb : d324659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271082, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d271082, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d271083 q = 1) (hb : d324660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271083, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271083, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271084 q = 1) (hb : d324661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271084, d324661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271084, d324661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104456 (p : Pattern) (ha : d271089 p = 1) (hb : d324671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d37648 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37657 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37707 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d324656 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d271080 q = 1) (hb : d324657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271080, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d271080, d324657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d37864 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d271081 q = 1) (hb : d324658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271081, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271081, d324658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d271082 q = 1) (hb : d324659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271082, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271082, d324659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271083 q = 1) (hb : d324660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271083, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d271083, d324660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d37874 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d37879 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d37882 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d324666 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d271085 q = 1) (hb : d324667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271085, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d271085, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d37889 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d271086 q = 1) (hb : d324668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271086, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d271086, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d271087 q = 1) (hb : d324669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271087, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d271087, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d271088 q = 1) (hb : d324670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271088, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d271088, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d271089 q = 1) (hb : d324671 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271089, d324671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d271089, d324671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104457 (p : Pattern) (ha : d271096 p = 1) (hb : d325181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d324666 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d271085 q = 1) (hb : d324667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271085, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271085, d324667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d37889 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271086 q = 1) (hb : d324668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271086, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271086, d324668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271094 q = 1) (hb : d324669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271094, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271094, d324669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271095 q = 1) (hb : d324670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271095, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271095, d324670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271096 q = 1) (hb : d325181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271096, d325181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271096, d325181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104458 (p : Pattern) (ha : d271106 p = 1) (hb : d325192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38025 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d325187 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d271102 q = 1) (hb : d325188 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271102, d325188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271102, d325188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38123 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271103 q = 1) (hb : d325189 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271103, d325189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271103, d325189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271104 q = 1) (hb : d325190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271104, d325190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271104, d325190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271105 q = 1) (hb : d325191 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271105, d325191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271105, d325191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271106 q = 1) (hb : d325192 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271106, d325192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271106, d325192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104459 (p : Pattern) (ha : d271112 p = 1) (hb : d325198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d37640 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271090 q = 1) (hb : d324672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271090, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104455 q ha hb
    | true =>
      simp only [d271090, d324672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104456 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37912 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d271091 q = 1) (hb : d324673 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271091, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271091, d324673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271092 q = 1) (hb : d325179 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271092, d325179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271092, d325179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271093 q = 1) (hb : d325180 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271093, d325180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d271093, d325180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271097 q = 1) (hb : d325182 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271097, d325182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271097, d325182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104457 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d37921 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d271098 q = 1) (hb : d325183 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271098, d325183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d271098, d325183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d271099 q = 1) (hb : d325184 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271099, d325184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d271099, d325184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d271100 q = 1) (hb : d325185 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271100, d325185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d271100, d325185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d271101 q = 1) (hb : d325186 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d271101, d325186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d271101, d325186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d271107 q = 1) (hb : d325193 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271107, d325193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271107, d325193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104458 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d38139 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d271108 q = 1) (hb : d325194 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271108, d325194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d271108, d325194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d271109 q = 1) (hb : d325195 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271109, d325195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d271109, d325195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d271110 q = 1) (hb : d325196 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271110, d325196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d271110, d325196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d271111 q = 1) (hb : d325197 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d271111, d325197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d271111, d325197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d271112 q = 1) (hb : d325198 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d271112, d325198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d271112, d325198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104460 (p : Pattern) (ha : d271118 p = 1) (hb : d325204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271113 q = 1) (hb : d325199 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d271113, d325199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271113, d325199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104459 q ha hb
  have h2 (q : Pattern) (ha : d271114 q = 1) (hb : d325200 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d271114, d325200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271114, d325200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271115 q = 1) (hb : d325201 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d271115, d325201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271115, d325201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271116 q = 1) (hb : d325202 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d271116, d325202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271116, d325202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271117 q = 1) (hb : d325203 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d271117, d325203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271117, d325203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271118 q = 1) (hb : d325204 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d271118, d325204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271118, d325204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104461 (p : Pattern) (ha : d46921 p = 1) (hb : d271127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38292 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38301 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d38329 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46917 q = 1) (hb : d271123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d271123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46917, d271123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d38470 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46918 q = 1) (hb : d271124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d271124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46918, d271124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46919 q = 1) (hb : d271125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d271125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46919, d271125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46920 q = 1) (hb : d271126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d271126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46920, d271126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46921 q = 1) (hb : d271127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46921, d271127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46921, d271127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104462 (p : Pattern) (ha : d46931 p = 1) (hb : d271132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d38292 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38301 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38329 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46917 q = 1) (hb : d271123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d271123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46917, d271123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d38470 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46918 q = 1) (hb : d271124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d271124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46918, d271124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46919 q = 1) (hb : d271125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d271125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46919, d271125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46920 q = 1) (hb : d271126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d271126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46920, d271126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d38480 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d38485 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d38488 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d46926 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d46927 q = 1) (hb : d271128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d271128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46927, d271128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d38495 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46928 q = 1) (hb : d271129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d271129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46928, d271129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46929 q = 1) (hb : d271130 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d271130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46929, d271130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46930 q = 1) (hb : d271131 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d271131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46930, d271131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46931 q = 1) (hb : d271132 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46931, d271132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46931, d271132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104463 (p : Pattern) (ha : d271139 p = 1) (hb : d321910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38488 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46926 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46927 q = 1) (hb : d271128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d271128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46927, d271128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38495 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46928 q = 1) (hb : d271129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d271129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46928, d271129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46929 q = 1) (hb : d271137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d271137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46929, d271137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46930 q = 1) (hb : d271138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d271138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46930, d271138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271139 q = 1) (hb : d321910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271139, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271139, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro104464 (p : Pattern) (ha : d271149 p = 1) (hb : d326605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38617 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d326600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d271145 q = 1) (hb : d326601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271145, d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d271145, d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38737 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271146 q = 1) (hb : d326602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271146, d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271146, d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271147 q = 1) (hb : d326603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271147, d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271147, d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271148 q = 1) (hb : d326604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271148, d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271148, d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271149 q = 1) (hb : d326605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271149, d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271149, d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104465 (p : Pattern) (ha : d271155 p = 1) (hb : d326611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d38284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46932 q = 1) (hb : d271133 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, d271133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104461 q ha hb
    | true =>
      simp only [d46932, d271133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104462 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38518 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46933 q = 1) (hb : d271134 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, d271134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46933, d271134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271135 q = 1) (hb : d321908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271135, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d271135, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271136 q = 1) (hb : d321909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271136, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d271136, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271140 q = 1) (hb : d321911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271140, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271140, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104463 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d38527 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d271141 q = 1) (hb : d321912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271141, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d271141, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d271142 q = 1) (hb : d321913 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271142, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d271142, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d271143 q = 1) (hb : d321914 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271143, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d271143, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d271144 q = 1) (hb : d321915 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d271144, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d271144, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d271150 q = 1) (hb : d326606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271150, d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271150, d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104464 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d38753 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d271151 q = 1) (hb : d326607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271151, d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d271151, d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d271152 q = 1) (hb : d326608 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271152, d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d271152, d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d271153 q = 1) (hb : d326609 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271153, d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d271153, d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d271154 q = 1) (hb : d326610 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d271154, d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d271154, d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d271155 q = 1) (hb : d326611 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d271155, d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d271155, d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104466 (p : Pattern) (ha : d271161 p = 1) (hb : d326617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271156 q = 1) (hb : d326612 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d271156, d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271156, d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104465 q ha hb
  have h2 (q : Pattern) (ha : d271157 q = 1) (hb : d326613 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d271157, d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271157, d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271158 q = 1) (hb : d326614 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d271158, d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271158, d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271159 q = 1) (hb : d326615 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d271159, d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271159, d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271160 q = 1) (hb : d326616 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d271160, d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271160, d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271161 q = 1) (hb : d326617 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d271161, d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271161, d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104467 (p : Pattern) (ha : d271167 p = 1) (hb : d326623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d270027 q = 1) (hb : d326517 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270027, d326517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104436 q ha hb
    | true =>
      simp only [d270027, d326517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104442 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d270067 q = 1) (hb : d326544 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270067, d326544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270067, d326544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104448 q ha hb
  have h3 (q : Pattern) (ha : d270068 q = 1) (hb : d326545 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270068, d326545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270068, d326545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270108 q = 1) (hb : d326572 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270108, d326572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270108, d326572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104454 q ha hb
  have h5 (q : Pattern) (ha : d270109 q = 1) (hb : d326573 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270109, d326573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270109, d326573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270110 q = 1) (hb : d326574 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d270110, d326574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270110, d326574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271119 q = 1) (hb : d325205 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d271119, d325205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271119, d325205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104460 q ha hb
  have h8 (q : Pattern) (ha : d271120 q = 1) (hb : d325206 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d271120, d325206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271120, d325206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d271121 q = 1) (hb : d325207 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d271121, d325207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271121, d325207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271122 q = 1) (hb : d326575 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d271122, d326575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d271122, d326575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d271162 q = 1) (hb : d326618 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d271162, d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271162, d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104466 q ha hb
  have h12 (q : Pattern) (ha : d271163 q = 1) (hb : d326619 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d271163, d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271163, d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d271164 q = 1) (hb : d326620 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d271164, d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271164, d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271165 q = 1) (hb : d326621 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d271165, d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271165, d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d271166 q = 1) (hb : d326622 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d271166, d326622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d271166, d326622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d271167 q = 1) (hb : d326623 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d271167, d326623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d271167, d326623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro104468 (p : Pattern) (ha : d271173 p = 1) (hb : d326629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271168 q = 1) (hb : d326624 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d271168, d326624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104467 q ha hb
    | true =>
      simp only [d271168, d326624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271169 q = 1) (hb : d326625 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d271169, d326625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271169, d326625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271170 q = 1) (hb : d326626 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d271170, d326626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271170, d326626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271171 q = 1) (hb : d326627 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d271171, d326627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271171, d326627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271172 q = 1) (hb : d326628 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d271172, d326628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271172, d326628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271173 q = 1) (hb : d326629 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d271173, d326629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271173, d326629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104469 (p : Pattern) (ha : d271179 p = 1) (hb : d326635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271174 q = 1) (hb : d326630 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d271174, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104468 q ha hb
    | true =>
      simp only [d271174, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271175 q = 1) (hb : d326631 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d271175, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271175, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271176 q = 1) (hb : d326632 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d271176, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271176, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271177 q = 1) (hb : d326633 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d271177, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271177, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271178 q = 1) (hb : d326634 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d271178, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271178, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271179 q = 1) (hb : d326635 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d271179, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271179, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104470 (p : Pattern) (ha : d271185 p = 1) (hb : d326641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271180 q = 1) (hb : d326636 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d271180, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104469 q ha hb
    | true =>
      simp only [d271180, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271181 q = 1) (hb : d326637 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d271181, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271181, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271182 q = 1) (hb : d326638 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d271182, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271182, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271183 q = 1) (hb : d326639 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d271183, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271183, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271184 q = 1) (hb : d326640 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d271184, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271184, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271185 q = 1) (hb : d326641 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d271185, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271185, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104471 (p : Pattern) (ha : d271191 p = 1) (hb : d326647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271186 q = 1) (hb : d326642 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d271186, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104470 q ha hb
    | true =>
      simp only [d271186, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271187 q = 1) (hb : d326643 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d271187, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271187, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271188 q = 1) (hb : d326644 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d271188, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271188, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271189 q = 1) (hb : d326645 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d271189, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271189, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271190 q = 1) (hb : d326646 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d271190, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271190, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271191 q = 1) (hb : d326647 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d271191, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271191, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104472 (p : Pattern) (ha : d271197 p = 1) (hb : d326653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271192 q = 1) (hb : d326648 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d271192, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104471 q ha hb
    | true =>
      simp only [d271192, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271193 q = 1) (hb : d326649 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d271193, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271193, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271194 q = 1) (hb : d326650 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d271194, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271194, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271195 q = 1) (hb : d326651 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d271195, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271195, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271196 q = 1) (hb : d326652 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d271196, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271196, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271197 q = 1) (hb : d326653 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d271197, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271197, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104473 (p : Pattern) (ha : d271203 p = 1) (hb : d326659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271198 q = 1) (hb : d326654 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d271198, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104472 q ha hb
    | true =>
      simp only [d271198, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271199 q = 1) (hb : d326655 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d271199, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271199, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271200 q = 1) (hb : d326656 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d271200, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271200, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271201 q = 1) (hb : d326657 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d271201, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271201, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271202 q = 1) (hb : d326658 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d271202, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271202, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271203 q = 1) (hb : d326659 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d271203, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271203, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104474 (p : Pattern) (ha : d271209 p = 1) (hb : d326665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271204 q = 1) (hb : d326660 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d271204, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104473 q ha hb
    | true =>
      simp only [d271204, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271205 q = 1) (hb : d326661 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d271205, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271205, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271206 q = 1) (hb : d326662 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d271206, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271206, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271207 q = 1) (hb : d326663 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d271207, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271207, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271208 q = 1) (hb : d326664 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d271208, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271208, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271209 q = 1) (hb : d326665 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d271209, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271209, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104475 (p : Pattern) (ha : d46466 p = 1) (hb : d271212 p = 1) : d370114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46461 q = 1) (hb : d271211 q = 1) : d46461 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46462 q = 1) (hb : d271212 q = 1) : d370110 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, d271212, d370110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46462, d271212, d370110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d46463 q = 1) (hb : d271212 q = 1) : d370111 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, d370111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46463, d370111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46464 q = 1) (hb : d271212 q = 1) : d370112 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, d370112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46464, d370112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46465 q = 1) (hb : d271212 q = 1) : d370113 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, d370113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46465, d370113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46466 q = 1) (hb : d271212 q = 1) : d370114 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46466, d370114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46466, d370114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro104476 (p : Pattern) (ha : d46482 p = 1) (hb : d271212 p = 1) : d370120 p = 1 := by
  have h0 (q : Pattern) (ha : d46461 q = 1) (hb : d271211 q = 1) : d46461 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46462 q = 1) (hb : d271212 q = 1) : d370110 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, d271212, d370110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46462, d271212, d370110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46463 q = 1) (hb : d271212 q = 1) : d370111 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, d370111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46463, d370111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46464 q = 1) (hb : d271212 q = 1) : d370112 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, d370112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46464, d370112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d46465 q = 1) (hb : d271212 q = 1) : d370113 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, d370113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46465, d370113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d46474 q = 1) (hb : d271211 q = 1) : d46474 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d46475 q = 1) (hb : d271212 q = 1) : d276467 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46475, d271212, d276467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46475, d271212, d276467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d46476 q = 1) (hb : d271212 q = 1) : d276487 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46476, d276487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46476, d276487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d46477 q = 1) (hb : d271211 q = 1) : d46477 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d19 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d46478 q = 1) (hb : d271212 q = 1) : d179204 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46478, d271212, d179204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46478, d271212, d179204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d46479 q = 1) (hb : d271212 q = 1) : d275501 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46479, d275501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46479, d275501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d46480 q = 1) (hb : d271212 q = 1) : d276488 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46480, d276488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46480, d276488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46481 q = 1) (hb : d271212 q = 1) : d276489 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46481, d276489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46481, d276489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d46482 q = 1) (hb : d271212 q = 1) : d370120 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46482, d370120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46482, d370120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro104477 (p : Pattern) (ha : d46488 p = 1) (hb : d271212 p = 1) : d370126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46467 q = 1) (hb : d271212 q = 1) : d370115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104475 q ha hb
    | true =>
      simp only [d46467, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46468 q = 1) (hb : d271212 q = 1) : d370116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46468, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46469 q = 1) (hb : d271212 q = 1) : d370117 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, d370117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46469, d370117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46470 q = 1) (hb : d271212 q = 1) : d370118 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, d370118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46470, d370118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46471 q = 1) (hb : d271212 q = 1) : d370119 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46471, d370119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46471, d370119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46483 q = 1) (hb : d271212 q = 1) : d370121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104476 q ha hb
    | true =>
      simp only [d46483, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46484 q = 1) (hb : d271212 q = 1) : d370122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46484, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46485 q = 1) (hb : d271212 q = 1) : d370123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46485, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46486 q = 1) (hb : d271212 q = 1) : d370124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46486, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d46487 q = 1) (hb : d271212 q = 1) : d370125 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, d370125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46487, d370125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46488 q = 1) (hb : d271212 q = 1) : d370126 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46488, d370126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46488, d370126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104478 (p : Pattern) (ha : d46490 p = 1) (hb : d271212 p = 1) : d370128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46467 q = 1) (hb : d271212 q = 1) : d370115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104475 q ha hb
    | true =>
      simp only [d46467, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46468 q = 1) (hb : d271212 q = 1) : d370116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46468, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46469 q = 1) (hb : d271212 q = 1) : d370117 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, d370117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46469, d370117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46470 q = 1) (hb : d271212 q = 1) : d370118 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, d370118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46470, d370118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46483 q = 1) (hb : d271212 q = 1) : d370121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104476 q ha hb
    | true =>
      simp only [d46483, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46484 q = 1) (hb : d271212 q = 1) : d370122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46484, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46485 q = 1) (hb : d271212 q = 1) : d370123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46485, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46486 q = 1) (hb : d271212 q = 1) : d370124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46486, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46487 q = 1) (hb : d271212 q = 1) : d370125 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, d370125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46487, d370125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46489 q = 1) (hb : d271212 q = 1) : d370127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46489, d370127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46489, d370127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46490 q = 1) (hb : d271212 q = 1) : d370128 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46490, d370128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46490, d370128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104479 (p : Pattern) (ha : d46494 p = 1) (hb : d271212 p = 1) : d276490 p = 1 := by
  have h0 (q : Pattern) (ha : d46474 q = 1) (hb : d271211 q = 1) : d46474 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46475 q = 1) (hb : d271212 q = 1) : d276467 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46475, d271212, d276467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46475, d271212, d276467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46476 q = 1) (hb : d271212 q = 1) : d276487 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46476, d276487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46476, d276487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46477 q = 1) (hb : d271211 q = 1) : d46477 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d19 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46478 q = 1) (hb : d271212 q = 1) : d179204 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46478, d271212, d179204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46478, d271212, d179204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d46479 q = 1) (hb : d271212 q = 1) : d275501 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46479, d275501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46479, d275501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d46480 q = 1) (hb : d271212 q = 1) : d276488 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46480, d276488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46480, d276488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46481 q = 1) (hb : d271212 q = 1) : d276489 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46481, d276489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46481, d276489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d46494 q = 1) (hb : d271212 q = 1) : d276490 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46494, d276490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46494, d276490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h11 p ha hb
theorem andIntro104480 (p : Pattern) (ha : d46500 p = 1) (hb : d271212 p = 1) : d370132 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46483 q = 1) (hb : d271212 q = 1) : d370121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104476 q ha hb
    | true =>
      simp only [d46483, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46484 q = 1) (hb : d271212 q = 1) : d370122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46484, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46485 q = 1) (hb : d271212 q = 1) : d370123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46485, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46486 q = 1) (hb : d271212 q = 1) : d370124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46486, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46489 q = 1) (hb : d271212 q = 1) : d370127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46489, d370127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46489, d370127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46495 q = 1) (hb : d271212 q = 1) : d276491 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46495, d276491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104479 q ha hb
    | true =>
      simp only [d46495, d276491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46496 q = 1) (hb : d271212 q = 1) : d276492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46496, d276492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46496, d276492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46497 q = 1) (hb : d271212 q = 1) : d276493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46497, d276493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46497, d276493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46498 q = 1) (hb : d271212 q = 1) : d276494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46498, d276494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46498, d276494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d46499 q = 1) (hb : d271212 q = 1) : d276495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46499, d276495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46499, d276495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46500 q = 1) (hb : d271212 q = 1) : d370132 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46500, d370132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46500, d370132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104481 (p : Pattern) (ha : d46507 p = 1) (hb : d271212 p = 1) : d370139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46491 q = 1) (hb : d271212 q = 1) : d370129 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, d370129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104477 q ha hb
    | true =>
      simp only [d46491, d370129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104478 q ha hb
  have h2 (q : Pattern) (ha : d46492 q = 1) (hb : d271212 q = 1) : d370130 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, d370130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46492, d370130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46493 q = 1) (hb : d271212 q = 1) : d370131 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, d370131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46493, d370131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46501 q = 1) (hb : d271212 q = 1) : d370133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, d370133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104478 q ha hb
    | true =>
      simp only [d46501, d370133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104480 q ha hb
  have h5 (q : Pattern) (ha : d46502 q = 1) (hb : d271212 q = 1) : d370134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, d370134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46502, d370134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46503 q = 1) (hb : d271212 q = 1) : d370135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, d370135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46503, d370135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46504 q = 1) (hb : d271212 q = 1) : d370136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, d370136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46504, d370136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46505 q = 1) (hb : d271212 q = 1) : d370137 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46505, d370137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46505, d370137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46506 q = 1) (hb : d271212 q = 1) : d370138 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46506, d370138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46506, d370138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46507 q = 1) (hb : d271212 q = 1) : d370139 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46507, d370139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46507, d370139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro104482 (p : Pattern) (ha : d46511 p = 1) (hb : d271212 p = 1) : d370143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46501 q = 1) (hb : d271212 q = 1) : d370133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, d370133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104478 q ha hb
    | true =>
      simp only [d46501, d370133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104480 q ha hb
  have h2 (q : Pattern) (ha : d46502 q = 1) (hb : d271212 q = 1) : d370134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, d370134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46502, d370134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46503 q = 1) (hb : d271212 q = 1) : d370135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, d370135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46503, d370135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46505 q = 1) (hb : d271212 q = 1) : d370137 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46505, d370137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46505, d370137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46510 q = 1) (hb : d271212 q = 1) : d370142 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46510, d370142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46510, d370142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46511 q = 1) (hb : d271212 q = 1) : d370143 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46511, d370143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46511, d370143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104483 (p : Pattern) (ha : d46517 p = 1) (hb : d271212 p = 1) : d370149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46508 q = 1) (hb : d271212 q = 1) : d370140 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104481 q ha hb
    | true =>
      simp only [d46508, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46509 q = 1) (hb : d271212 q = 1) : d370141 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46509, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46512 q = 1) (hb : d271212 q = 1) : d370144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104482 q ha hb
    | true =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46513 q = 1) (hb : d271212 q = 1) : d370145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46514 q = 1) (hb : d271212 q = 1) : d370146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46515 q = 1) (hb : d271212 q = 1) : d370147 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46515, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46516 q = 1) (hb : d271212 q = 1) : d370148 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46516, d370148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46516, d370148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46517 q = 1) (hb : d271212 q = 1) : d370149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46517, d370149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46517, d370149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104484 (p : Pattern) (ha : d46521 p = 1) (hb : d271212 p = 1) : d370153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46512 q = 1) (hb : d271212 q = 1) : d370144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104482 q ha hb
    | true =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46513 q = 1) (hb : d271212 q = 1) : d370145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46518 q = 1) (hb : d271212 q = 1) : d370150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46519 q = 1) (hb : d271212 q = 1) : d370151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46519, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46520 q = 1) (hb : d271212 q = 1) : d370152 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46520, d370152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46520, d370152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46521 q = 1) (hb : d271212 q = 1) : d370153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46521, d370153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46521, d370153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104485 (p : Pattern) (ha : d46527 p = 1) (hb : d271212 p = 1) : d370159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46522 q = 1) (hb : d271212 q = 1) : d370154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104483 q ha hb
    | true =>
      simp only [d46522, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104484 q ha hb
  have h2 (q : Pattern) (ha : d46523 q = 1) (hb : d271212 q = 1) : d370155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46523, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46524 q = 1) (hb : d271212 q = 1) : d370156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46524, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46525 q = 1) (hb : d271212 q = 1) : d370157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46525, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46526 q = 1) (hb : d271212 q = 1) : d370158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46526, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46527 q = 1) (hb : d271212 q = 1) : d370159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46527, d370159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46527, d370159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104486 (p : Pattern) (ha : d46530 p = 1) (hb : d271212 p = 1) : d370162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46508 q = 1) (hb : d271212 q = 1) : d370140 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104481 q ha hb
    | true =>
      simp only [d46508, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46509 q = 1) (hb : d271212 q = 1) : d370141 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46509, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46512 q = 1) (hb : d271212 q = 1) : d370144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104482 q ha hb
    | true =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46513 q = 1) (hb : d271212 q = 1) : d370145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46514 q = 1) (hb : d271212 q = 1) : d370146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46515 q = 1) (hb : d271212 q = 1) : d370147 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46515, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46516 q = 1) (hb : d271212 q = 1) : d370148 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46516, d370148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46516, d370148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46530 q = 1) (hb : d271212 q = 1) : d370162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46530, d370162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46530, d370162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104487 (p : Pattern) (ha : d46531 p = 1) (hb : d271212 p = 1) : d370163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46512 q = 1) (hb : d271212 q = 1) : d370144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104482 q ha hb
    | true =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46513 q = 1) (hb : d271212 q = 1) : d370145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46518 q = 1) (hb : d271212 q = 1) : d370150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46519 q = 1) (hb : d271212 q = 1) : d370151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46519, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46520 q = 1) (hb : d271212 q = 1) : d370152 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46520, d370152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46520, d370152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46531 q = 1) (hb : d271212 q = 1) : d370163 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46531, d370163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46531, d370163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104488 (p : Pattern) (ha : d46537 p = 1) (hb : d271212 p = 1) : d370169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46522 q = 1) (hb : d271212 q = 1) : d370154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104483 q ha hb
    | true =>
      simp only [d46522, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104484 q ha hb
  have h2 (q : Pattern) (ha : d46523 q = 1) (hb : d271212 q = 1) : d370155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46523, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46524 q = 1) (hb : d271212 q = 1) : d370156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46524, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46525 q = 1) (hb : d271212 q = 1) : d370157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46525, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46526 q = 1) (hb : d271212 q = 1) : d370158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46526, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46532 q = 1) (hb : d271212 q = 1) : d370164 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, d370164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104486 q ha hb
    | true =>
      simp only [d46532, d370164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104487 q ha hb
  have h7 (q : Pattern) (ha : d46533 q = 1) (hb : d271212 q = 1) : d370165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d370165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46533, d370165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46534 q = 1) (hb : d271212 q = 1) : d370166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d370166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46534, d370166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46535 q = 1) (hb : d271212 q = 1) : d370167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d370167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46535, d370167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46536 q = 1) (hb : d271212 q = 1) : d370168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d370168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46536, d370168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46537 q = 1) (hb : d271212 q = 1) : d370169 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46537, d370169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46537, d370169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104489 (p : Pattern) (ha : d46693 p = 1) (hb : d271212 p = 1) : d370258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46522 q = 1) (hb : d271212 q = 1) : d370154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104483 q ha hb
    | true =>
      simp only [d46522, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104484 q ha hb
  have h2 (q : Pattern) (ha : d46523 q = 1) (hb : d271212 q = 1) : d370155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46523, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46524 q = 1) (hb : d271212 q = 1) : d370156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46524, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46525 q = 1) (hb : d271212 q = 1) : d370157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46525, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46526 q = 1) (hb : d271212 q = 1) : d370158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46526, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46688 q = 1) (hb : d271212 q = 1) : d370253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46688, d370253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104484 q ha hb
    | true =>
      simp only [d46688, d370253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46689 q = 1) (hb : d271212 q = 1) : d370254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46689, d370254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46689, d370254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46690 q = 1) (hb : d271212 q = 1) : d370255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46690, d370255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46690, d370255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46691 q = 1) (hb : d271212 q = 1) : d370256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46691, d370256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46691, d370256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46692 q = 1) (hb : d271212 q = 1) : d370257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46692, d370257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46692, d370257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46693 q = 1) (hb : d271212 q = 1) : d370258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46693, d370258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46693, d370258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104490 (p : Pattern) (ha : d46699 p = 1) (hb : d271212 p = 1) : d370264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46688 q = 1) (hb : d271212 q = 1) : d370253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46688, d370253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104484 q ha hb
    | true =>
      simp only [d46688, d370253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46689 q = 1) (hb : d271212 q = 1) : d370254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46689, d370254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46689, d370254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46690 q = 1) (hb : d271212 q = 1) : d370255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46690, d370255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46690, d370255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46691 q = 1) (hb : d271212 q = 1) : d370256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46691, d370256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46691, d370256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46692 q = 1) (hb : d271212 q = 1) : d370257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46692, d370257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46692, d370257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46694 q = 1) (hb : d271212 q = 1) : d370259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46694, d370259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104487 q ha hb
    | true =>
      simp only [d46694, d370259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46695 q = 1) (hb : d271212 q = 1) : d370260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46695, d370260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46695, d370260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46696 q = 1) (hb : d271212 q = 1) : d370261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46696, d370261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46696, d370261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46697 q = 1) (hb : d271212 q = 1) : d370262 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46697, d370262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46697, d370262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46698 q = 1) (hb : d271212 q = 1) : d370263 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46698, d370263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46698, d370263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46699 q = 1) (hb : d271212 q = 1) : d370264 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46699, d370264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46699, d370264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104491 (p : Pattern) (ha : d46708 p = 1) (hb : d271212 p = 1) : d370273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46694 q = 1) (hb : d271212 q = 1) : d370259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46694, d370259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104487 q ha hb
    | true =>
      simp only [d46694, d370259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46695 q = 1) (hb : d271212 q = 1) : d370260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46695, d370260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46695, d370260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46696 q = 1) (hb : d271212 q = 1) : d370261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46696, d370261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46696, d370261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46697 q = 1) (hb : d271212 q = 1) : d370262 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46697, d370262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46697, d370262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46698 q = 1) (hb : d271212 q = 1) : d370263 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46698, d370263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46698, d370263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46708 q = 1) (hb : d271212 q = 1) : d370273 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46708, d370273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46708, d370273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104492 (p : Pattern) (ha : d46730 p = 1) (hb : d271212 p = 1) : d370295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46714 q = 1) (hb : d271212 q = 1) : d370279 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, d370279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46714, d370279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104475 q ha hb
  have h2 (q : Pattern) (ha : d46467 q = 1) (hb : d271212 q = 1) : d370115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104475 q ha hb
    | true =>
      simp only [d46467, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46715 q = 1) (hb : d271212 q = 1) : d370280 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, d370280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46715, d370280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46468 q = 1) (hb : d271212 q = 1) : d370116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46468, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46716 q = 1) (hb : d271212 q = 1) : d370281 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, d370281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46716, d370281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46717 q = 1) (hb : d271212 q = 1) : d370282 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, d370282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46717, d370282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46720 q = 1) (hb : d271212 q = 1) : d370285 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, d370285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46720, d370285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104476 q ha hb
  have h8 (q : Pattern) (ha : d46483 q = 1) (hb : d271212 q = 1) : d370121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104476 q ha hb
    | true =>
      simp only [d46483, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46721 q = 1) (hb : d271212 q = 1) : d370286 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, d370286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46721, d370286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46484 q = 1) (hb : d271212 q = 1) : d370122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46484, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46722 q = 1) (hb : d271212 q = 1) : d370287 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, d370287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46722, d370287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46723 q = 1) (hb : d271212 q = 1) : d370288 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, d370288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46723, d370288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d46724 q = 1) (hb : d271212 q = 1) : d370289 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, d370289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46724, d370289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46729 q = 1) (hb : d271212 q = 1) : d370294 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46729, d370294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46729, d370294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d46730 q = 1) (hb : d271212 q = 1) : d370295 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46730, d370295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46730, d370295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104493 (p : Pattern) (ha : d46740 p = 1) (hb : d271212 p = 1) : d370300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46720 q = 1) (hb : d271212 q = 1) : d370285 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, d370285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46720, d370285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104476 q ha hb
  have h2 (q : Pattern) (ha : d46483 q = 1) (hb : d271212 q = 1) : d370121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104476 q ha hb
    | true =>
      simp only [d46483, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46721 q = 1) (hb : d271212 q = 1) : d370286 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, d370286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46721, d370286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46484 q = 1) (hb : d271212 q = 1) : d370122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46484, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46722 q = 1) (hb : d271212 q = 1) : d370287 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, d370287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46722, d370287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46723 q = 1) (hb : d271212 q = 1) : d370288 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, d370288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46723, d370288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46729 q = 1) (hb : d271212 q = 1) : d370294 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46729, d370294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46729, d370294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46735 q = 1) (hb : d271212 q = 1) : d276731 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46735, d276731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46735, d276731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104479 q ha hb
  have h9 (q : Pattern) (ha : d46495 q = 1) (hb : d271212 q = 1) : d276491 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46495, d276491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104479 q ha hb
    | true =>
      simp only [d46495, d276491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d46736 q = 1) (hb : d271212 q = 1) : d276732 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46736, d276732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46736, d276732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46496 q = 1) (hb : d271212 q = 1) : d276492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46496, d276492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46496, d276492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46737 q = 1) (hb : d271212 q = 1) : d276733 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46737, d276733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46737, d276733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46738 q = 1) (hb : d271212 q = 1) : d276734 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46738, d276734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46738, d276734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d46739 q = 1) (hb : d271212 q = 1) : d276735 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46739, d276735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46739, d276735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d46740 q = 1) (hb : d271212 q = 1) : d370300 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46740, d370300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46740, d370300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104494 (p : Pattern) (ha : d46759 p = 1) (hb : d271212 p = 1) : d370319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46741 q = 1) (hb : d271212 q = 1) : d370301 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, d370301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104492 q ha hb
    | true =>
      simp only [d46741, d370301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104493 q ha hb
  have h2 (q : Pattern) (ha : d46742 q = 1) (hb : d271212 q = 1) : d370302 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, d370302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46742, d370302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46743 q = 1) (hb : d271212 q = 1) : d370303 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, d370303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46743, d370303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46749 q = 1) (hb : d271212 q = 1) : d370309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46749, d370309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46749, d370309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46758 q = 1) (hb : d271212 q = 1) : d370318 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46758, d370318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46758, d370318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46759 q = 1) (hb : d271212 q = 1) : d370319 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46759, d370319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46759, d370319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104495 (p : Pattern) (ha : d46841 p = 1) (hb : d271212 p = 1) : d370357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46760 q = 1) (hb : d271212 q = 1) : d370320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46760, d370320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104494 q ha hb
    | true =>
      simp only [d46760, d370320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46761 q = 1) (hb : d271212 q = 1) : d370321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46761, d370321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46761, d370321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46838 q = 1) (hb : d271212 q = 1) : d370354 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46838, d370354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46838, d370354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46839 q = 1) (hb : d271212 q = 1) : d370355 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46839, d370355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46839, d370355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46840 q = 1) (hb : d271212 q = 1) : d370356 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46840, d370356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46840, d370356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46841 q = 1) (hb : d271212 q = 1) : d370357 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46841, d370357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46841, d370357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104496 (p : Pattern) (ha : d46847 p = 1) (hb : d271212 p = 1) : d370363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46842 q = 1) (hb : d271212 q = 1) : d370358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46842, d370358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104495 q ha hb
    | true =>
      simp only [d46842, d370358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46843 q = 1) (hb : d271212 q = 1) : d370359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46843, d370359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46843, d370359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46844 q = 1) (hb : d271212 q = 1) : d370360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46844, d370360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46844, d370360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46845 q = 1) (hb : d271212 q = 1) : d370361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46845, d370361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46845, d370361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46846 q = 1) (hb : d271212 q = 1) : d370362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46846, d370362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46846, d370362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46847 q = 1) (hb : d271212 q = 1) : d370363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46847, d370363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46847, d370363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104497 (p : Pattern) (ha : d46542 p = 1) (hb : d271212 p = 1) : d370174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46508 q = 1) (hb : d271212 q = 1) : d370140 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104481 q ha hb
    | true =>
      simp only [d46508, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46509 q = 1) (hb : d271212 q = 1) : d370141 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46509, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46512 q = 1) (hb : d271212 q = 1) : d370144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104482 q ha hb
    | true =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46513 q = 1) (hb : d271212 q = 1) : d370145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46514 q = 1) (hb : d271212 q = 1) : d370146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46515 q = 1) (hb : d271212 q = 1) : d370147 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46515, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46541 q = 1) (hb : d271212 q = 1) : d370173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46541, d370173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46541, d370173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46542 q = 1) (hb : d271212 q = 1) : d370174 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46542, d370174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46542, d370174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104498 (p : Pattern) (ha : d46544 p = 1) (hb : d271212 p = 1) : d370176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46512 q = 1) (hb : d271212 q = 1) : d370144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104482 q ha hb
    | true =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46513 q = 1) (hb : d271212 q = 1) : d370145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46518 q = 1) (hb : d271212 q = 1) : d370150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46519 q = 1) (hb : d271212 q = 1) : d370151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46519, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46543 q = 1) (hb : d271212 q = 1) : d370175 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46543, d370175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46543, d370175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46544 q = 1) (hb : d271212 q = 1) : d370176 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46544, d370176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46544, d370176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104499 (p : Pattern) (ha : d46551 p = 1) (hb : d271212 p = 1) : d370183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46508 q = 1) (hb : d271212 q = 1) : d370140 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104481 q ha hb
    | true =>
      simp only [d46508, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46509 q = 1) (hb : d271212 q = 1) : d370141 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46509, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46512 q = 1) (hb : d271212 q = 1) : d370144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104482 q ha hb
    | true =>
      simp only [d46512, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46513 q = 1) (hb : d271212 q = 1) : d370145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46514 q = 1) (hb : d271212 q = 1) : d370146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46549 q = 1) (hb : d271212 q = 1) : d370181 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46549, d370181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46549, d370181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46550 q = 1) (hb : d271212 q = 1) : d370182 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46550, d370182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46550, d370182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46551 q = 1) (hb : d271212 q = 1) : d370183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46551, d370183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46551, d370183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
