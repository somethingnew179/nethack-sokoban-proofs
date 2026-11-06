import NetHack.Soko22Hazard87.AndIntroBlocks0115
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro29000 (p : Pattern) (ha : d93045 p = 1) (hb : d116648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93040 q = 1) (hb : d116295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93040, d116295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28876 q ha hb
    | true =>
      simp only [d93040, d116295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93041 q = 1) (hb : d116296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93041, d116296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93041, d116296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28842 q ha hb
    | true =>
      simp only [d13523, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93042 q = 1) (hb : d116645 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93042, d116645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93042, d116645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93043 q = 1) (hb : d116646 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93043, d116646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93043, d116646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93044 q = 1) (hb : d116647 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93044, d116647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93044, d116647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93045 q = 1) (hb : d116648 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93045, d116648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93045, d116648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29001 (p : Pattern) (ha : d93057 p = 1) (hb : d116654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93037 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d93046 q = 1) (hb : d116649 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93046, d116649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29000 q ha hb
    | true =>
      simp only [d93046, d116649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28843 q hb ha
  have h3 (q : Pattern) (ha : d93047 q = 1) (hb : d116650 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93047, d116650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93047, d116650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93053 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93054 q = 1) (hb : d116651 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93054, d116651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93054, d116651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93055 q = 1) (hb : d116652 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93055, d116652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93055, d116652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93056 q = 1) (hb : d116653 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93056, d116653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93056, d116653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93057 q = 1) (hb : d116654 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93057, d116654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93057, d116654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29002 (p : Pattern) (ha : d93063 p = 1) (hb : d116660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92947 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93005 q = 1) (hb : d116190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93005, d116190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28997 q ha hb
    | true =>
      simp only [d93005, d116190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28998 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93013 q = 1) (hb : d116191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93013, d116191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93013, d116191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93014 q = 1) (hb : d116637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93014, d116637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93014, d116637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93015 q = 1) (hb : d116638 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93015, d116638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93015, d116638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93019 q = 1) (hb : d116640 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93019, d116640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93019, d116640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28999 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d93020 q = 1) (hb : d116641 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93020, d116641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93020, d116641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d93021 q = 1) (hb : d116642 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93021, d116642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93021, d116642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d93022 q = 1) (hb : d116643 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93022, d116643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93022, d116643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d93023 q = 1) (hb : d116644 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93023, d116644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93023, d116644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93058 q = 1) (hb : d116655 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93058, d116655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93058, d116655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29001 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93059 q = 1) (hb : d116656 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93059, d116656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93059, d116656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d93060 q = 1) (hb : d116657 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93060, d116657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93060, d116657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d93061 q = 1) (hb : d116658 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93061, d116658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93061, d116658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d93062 q = 1) (hb : d116659 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93062, d116659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93062, d116659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d93063 q = 1) (hb : d116660 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93063, d116660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93063, d116660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29003 (p : Pattern) (ha : d93069 p = 1) (hb : d116666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93064 q = 1) (hb : d116661 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93064, d116661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93064, d116661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29002 q ha hb
  have h2 (q : Pattern) (ha : d93065 q = 1) (hb : d116662 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93065, d116662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93065, d116662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93066 q = 1) (hb : d116663 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93066, d116663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93066, d116663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93067 q = 1) (hb : d116664 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93067, d116664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93067, d116664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93068 q = 1) (hb : d116665 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93068, d116665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93068, d116665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93069 q = 1) (hb : d116666 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93069, d116666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93069, d116666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29004 (p : Pattern) (ha : d93136 p = 1) (hb : d116337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93111 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93125 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93082 q = 1) (hb : d116332 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93082, d116332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28892 q ha hb
    | true =>
      simp only [d93082, d116332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28883 q hb ha
  have h5 (q : Pattern) (ha : d93126 q = 1) (hb : d116333 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93126, d116333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d93126, d116333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d93132 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d93133 q = 1) (hb : d116334 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93133, d116334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93133, d116334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d93134 q = 1) (hb : d116335 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93134, d116335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93134, d116335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93135 q = 1) (hb : d116336 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93135, d116336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93135, d116336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93136 q = 1) (hb : d116337 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93136, d116337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93136, d116337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29005 (p : Pattern) (ha : d93156 p = 1) (hb : d116346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d93105 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93111 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93082 q = 1) (hb : d116332 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93082, d116332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28892 q ha hb
    | true =>
      simp only [d93082, d116332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28883 q hb ha
  have h4 (q : Pattern) (ha : d93126 q = 1) (hb : d116333 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93126, d116333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93126, d116333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d93132 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93133 q = 1) (hb : d116334 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93133, d116334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93133, d116334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93134 q = 1) (hb : d116335 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93134, d116335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93134, d116335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93135 q = 1) (hb : d116336 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93135, d116336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93135, d116336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d93141 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d93145 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d93148 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d93091 q = 1) (hb : d116341 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93091, d116341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28894 q ha hb
    | true =>
      simp only [d93091, d116341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28884 q hb ha
  have h13 (q : Pattern) (ha : d93149 q = 1) (hb : d116342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93149, d116342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d93149, d116342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d93152 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93153 q = 1) (hb : d116343 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93153, d116343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93153, d116343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d93154 q = 1) (hb : d116344 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93154, d116344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d93154, d116344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93155 q = 1) (hb : d116345 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93155, d116345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d93155, d116345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93156 q = 1) (hb : d116346 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93156, d116346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93156, d116346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29006 (p : Pattern) (ha : d93170 p = 1) (hb : d116673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93148 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d93091 q = 1) (hb : d116341 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93091, d116341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28894 q ha hb
    | true =>
      simp only [d93091, d116341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28884 q hb ha
  have h3 (q : Pattern) (ha : d93149 q = 1) (hb : d116342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93149, d116342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93149, d116342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93152 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93153 q = 1) (hb : d116343 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93153, d116343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93153, d116343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93168 q = 1) (hb : d116344 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93168, d116344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93168, d116344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93169 q = 1) (hb : d116345 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93169, d116345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93169, d116345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93170 q = 1) (hb : d116673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93170, d116673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93170, d116673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29007 (p : Pattern) (ha : d93197 p = 1) (hb : d116682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93192 q = 1) (hb : d116452 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93192, d116452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28922 q ha hb
    | true =>
      simp only [d93192, d116452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93193 q = 1) (hb : d116453 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93193, d116453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93193, d116453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28888 q ha hb
    | true =>
      simp only [d13850, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93194 q = 1) (hb : d116679 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93194, d116679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93194, d116679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93195 q = 1) (hb : d116680 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93195, d116680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93195, d116680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93196 q = 1) (hb : d116681 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93196, d116681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93196, d116681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93197 q = 1) (hb : d116682 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93197, d116682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93197, d116682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29008 (p : Pattern) (ha : d93209 p = 1) (hb : d116688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d93198 q = 1) (hb : d116683 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93198, d116683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29007 q ha hb
    | true =>
      simp only [d93198, d116683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28889 q hb ha
  have h3 (q : Pattern) (ha : d93199 q = 1) (hb : d116684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93199, d116684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93199, d116684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93205 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93206 q = 1) (hb : d116685 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93206, d116685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93206, d116685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93207 q = 1) (hb : d116686 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93207, d116686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93207, d116686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93208 q = 1) (hb : d116687 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93208, d116687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93208, d116687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93209 q = 1) (hb : d116688 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93209, d116688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93209, d116688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29009 (p : Pattern) (ha : d93215 p = 1) (hb : d116694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d93099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93157 q = 1) (hb : d116347 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93157, d116347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29004 q ha hb
    | true =>
      simp only [d93157, d116347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29005 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93165 q = 1) (hb : d116348 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93165, d116348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93165, d116348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93166 q = 1) (hb : d116671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93166, d116671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93166, d116671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93167 q = 1) (hb : d116672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93167, d116672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93167, d116672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93171 q = 1) (hb : d116674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93171, d116674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93171, d116674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29006 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d93172 q = 1) (hb : d116675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93172, d116675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93172, d116675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d93173 q = 1) (hb : d116676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93173, d116676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93173, d116676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d93174 q = 1) (hb : d116677 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93174, d116677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93174, d116677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d93175 q = 1) (hb : d116678 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93175, d116678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93175, d116678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93210 q = 1) (hb : d116689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93210, d116689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93210, d116689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29008 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93211 q = 1) (hb : d116690 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93211, d116690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93211, d116690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d93212 q = 1) (hb : d116691 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93212, d116691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93212, d116691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d93213 q = 1) (hb : d116692 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93213, d116692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93213, d116692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d93214 q = 1) (hb : d116693 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93214, d116693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93214, d116693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d93215 q = 1) (hb : d116694 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93215, d116694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93215, d116694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29010 (p : Pattern) (ha : d93221 p = 1) (hb : d116700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93216 q = 1) (hb : d116695 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93216, d116695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93216, d116695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29009 q ha hb
  have h2 (q : Pattern) (ha : d93217 q = 1) (hb : d116696 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93217, d116696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93217, d116696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93218 q = 1) (hb : d116697 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93218, d116697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93218, d116697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93219 q = 1) (hb : d116698 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93219, d116698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93219, d116698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93220 q = 1) (hb : d116699 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93220, d116699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93220, d116699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93221 q = 1) (hb : d116700 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93221, d116700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93221, d116700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29011 (p : Pattern) (ha : d93227 p = 1) (hb : d116706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d92620 q = 1) (hb : d116575 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92620, d116575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28975 q ha hb
    | true =>
      simp only [d92620, d116575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28982 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92769 q = 1) (hb : d116602 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92769, d116602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92769, d116602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28989 q ha hb
  have h3 (q : Pattern) (ha : d92770 q = 1) (hb : d116603 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d92770, d116603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d92770, d116603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92919 q = 1) (hb : d116634 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92919, d116634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92919, d116634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28996 q ha hb
  have h5 (q : Pattern) (ha : d92920 q = 1) (hb : d116635 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d92920, d116635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92920, d116635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92921 q = 1) (hb : d116636 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d92921, d116636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92921, d116636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93070 q = 1) (hb : d116667 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d93070, d116667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93070, d116667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29003 q ha hb
  have h8 (q : Pattern) (ha : d93071 q = 1) (hb : d116668 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d93071, d116668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93071, d116668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93072 q = 1) (hb : d116669 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d93072, d116669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93072, d116669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93073 q = 1) (hb : d116670 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d93073, d116670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93073, d116670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93222 q = 1) (hb : d116701 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d93222, d116701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93222, d116701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29010 q ha hb
  have h12 (q : Pattern) (ha : d93223 q = 1) (hb : d116702 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d93223, d116702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93223, d116702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93224 q = 1) (hb : d116703 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d93224, d116703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93224, d116703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d93225 q = 1) (hb : d116704 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d93225, d116704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93225, d116704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d93226 q = 1) (hb : d116705 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d93226, d116705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93226, d116705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93227 q = 1) (hb : d116706 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d93227, d116706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93227, d116706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro29012 (p : Pattern) (ha : d93233 p = 1) (hb : d116712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93228 q = 1) (hb : d116707 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d93228, d116707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29011 q ha hb
    | true =>
      simp only [d93228, d116707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93229 q = 1) (hb : d116708 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d93229, d116708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93229, d116708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93230 q = 1) (hb : d116709 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d93230, d116709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93230, d116709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93231 q = 1) (hb : d116710 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d93231, d116710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93231, d116710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93232 q = 1) (hb : d116711 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d93232, d116711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93232, d116711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93233 q = 1) (hb : d116712 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d93233, d116712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93233, d116712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29013 (p : Pattern) (ha : d93239 p = 1) (hb : d116718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93234 q = 1) (hb : d116713 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d93234, d116713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29012 q ha hb
    | true =>
      simp only [d93234, d116713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93235 q = 1) (hb : d116714 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d93235, d116714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93235, d116714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93236 q = 1) (hb : d116715 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d93236, d116715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93236, d116715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93237 q = 1) (hb : d116716 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d93237, d116716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93237, d116716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93238 q = 1) (hb : d116717 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d93238, d116717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93238, d116717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93239 q = 1) (hb : d116718 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d93239, d116718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93239, d116718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29014 (p : Pattern) (ha : d93245 p = 1) (hb : d116724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93240 q = 1) (hb : d116719 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d93240, d116719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29013 q ha hb
    | true =>
      simp only [d93240, d116719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93241 q = 1) (hb : d116720 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d93241, d116720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93241, d116720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93242 q = 1) (hb : d116721 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d93242, d116721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93242, d116721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93243 q = 1) (hb : d116722 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d93243, d116722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93243, d116722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93244 q = 1) (hb : d116723 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d93244, d116723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93244, d116723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93245 q = 1) (hb : d116724 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d93245, d116724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93245, d116724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29015 (p : Pattern) (ha : d93251 p = 1) (hb : d116730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93246 q = 1) (hb : d116725 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d93246, d116725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29014 q ha hb
    | true =>
      simp only [d93246, d116725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93247 q = 1) (hb : d116726 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d93247, d116726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93247, d116726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93248 q = 1) (hb : d116727 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d93248, d116727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93248, d116727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93249 q = 1) (hb : d116728 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d93249, d116728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93249, d116728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93250 q = 1) (hb : d116729 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d93250, d116729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93250, d116729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93251 q = 1) (hb : d116730 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d93251, d116730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93251, d116730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29016 (p : Pattern) (ha : d93257 p = 1) (hb : d116736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93252 q = 1) (hb : d116731 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d93252, d116731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29015 q ha hb
    | true =>
      simp only [d93252, d116731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93253 q = 1) (hb : d116732 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d93253, d116732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93253, d116732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93254 q = 1) (hb : d116733 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d93254, d116733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93254, d116733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93255 q = 1) (hb : d116734 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d93255, d116734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93255, d116734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93256 q = 1) (hb : d116735 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d93256, d116735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93256, d116735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93257 q = 1) (hb : d116736 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d93257, d116736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93257, d116736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29017 (p : Pattern) (ha : d93263 p = 1) (hb : d116742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93258 q = 1) (hb : d116737 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d93258, d116737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29016 q ha hb
    | true =>
      simp only [d93258, d116737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93259 q = 1) (hb : d116738 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d93259, d116738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93259, d116738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93260 q = 1) (hb : d116739 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d93260, d116739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93260, d116739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93261 q = 1) (hb : d116740 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d93261, d116740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93261, d116740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93262 q = 1) (hb : d116741 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d93262, d116741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93262, d116741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93263 q = 1) (hb : d116742 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d93263, d116742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93263, d116742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29018 (p : Pattern) (ha : d93269 p = 1) (hb : d116748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93264 q = 1) (hb : d116743 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d93264, d116743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29017 q ha hb
    | true =>
      simp only [d93264, d116743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93265 q = 1) (hb : d116744 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d93265, d116744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93265, d116744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93266 q = 1) (hb : d116745 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d93266, d116745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93266, d116745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93267 q = 1) (hb : d116746 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d93267, d116746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93267, d116746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93268 q = 1) (hb : d116747 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d93268, d116747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93268, d116747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93269 q = 1) (hb : d116748 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d93269, d116748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93269, d116748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29019 (p : Pattern) (ha : d94229 p = 1) (hb : d115637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8320 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d115583 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94225 q = 1) (hb : d115633 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94225, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8336 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94226 q = 1) (hb : d115634 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94226, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94227 q = 1) (hb : d115635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94227, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94228 q = 1) (hb : d115636 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94228, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94229 q = 1) (hb : d115637 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94229, d115637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94229, d115637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29020 (p : Pattern) (ha : d94234 p = 1) (hb : d115644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8320 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d115583 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94225 q = 1) (hb : d115633 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94225, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8336 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94226 q = 1) (hb : d115634 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94226, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94227 q = 1) (hb : d115635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94227, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94228 q = 1) (hb : d115636 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94228, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8345 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8349 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8351 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d115590 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94230 q = 1) (hb : d115640 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d115640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94230, d115640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94231 q = 1) (hb : d115641 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d115641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94231, d115641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94232 q = 1) (hb : d115642 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94232, d115642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94232, d115642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94233 q = 1) (hb : d115643 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94233, d115643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94233, d115643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94234 q = 1) (hb : d115644 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94234, d115644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94234, d115644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29021 (p : Pattern) (ha : d94241 p = 1) (hb : d116526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d115590 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94230 q = 1) (hb : d115640 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d115640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94230, d115640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94231 q = 1) (hb : d115641 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d115641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94231, d115641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94239 q = 1) (hb : d115642 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94239, d115642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94239, d115642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94240 q = 1) (hb : d115643 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94240, d115643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94240, d115643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94241 q = 1) (hb : d116526 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94241, d116526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94241, d116526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29022 (p : Pattern) (ha : d94251 p = 1) (hb : d116536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8384 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d115616 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94247 q = 1) (hb : d116532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94247, d116532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94247, d116532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8400 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94248 q = 1) (hb : d116533 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94248, d116533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94248, d116533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94249 q = 1) (hb : d116534 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94249, d116534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94249, d116534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94250 q = 1) (hb : d116535 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94250, d116535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94250, d116535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94251 q = 1) (hb : d116536 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94251, d116536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94251, d116536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29023 (p : Pattern) (ha : d94257 p = 1) (hb : d116542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94235 q = 1) (hb : d115645 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94235, d115645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29019 q ha hb
    | true =>
      simp only [d94235, d115645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29020 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8364 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94236 q = 1) (hb : d115646 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94236, d115646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94236, d115646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94237 q = 1) (hb : d116524 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94237, d116524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94237, d116524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94238 q = 1) (hb : d116525 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94238, d116525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94238, d116525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94242 q = 1) (hb : d116527 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94242, d116527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94242, d116527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29021 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94243 q = 1) (hb : d116528 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94243, d116528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94243, d116528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94244 q = 1) (hb : d116529 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94244, d116529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94244, d116529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94245 q = 1) (hb : d116530 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94245, d116530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94245, d116530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94246 q = 1) (hb : d116531 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94246, d116531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94246, d116531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94252 q = 1) (hb : d116537 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94252, d116537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94252, d116537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29022 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94253 q = 1) (hb : d116538 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94253, d116538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94253, d116538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94254 q = 1) (hb : d116539 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94254, d116539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94254, d116539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94255 q = 1) (hb : d116540 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94255, d116540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94255, d116540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94256 q = 1) (hb : d116541 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94256, d116541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94256, d116541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94257 q = 1) (hb : d116542 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94257, d116542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94257, d116542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29024 (p : Pattern) (ha : d94263 p = 1) (hb : d116548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d94220 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d94220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d94220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11648 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d94221 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d94221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d94221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d94222 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d94222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d94222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d94223 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d94223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d94223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d94224 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d94224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d94224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94258 q = 1) (hb : d116543 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94258, d116543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94258, d116543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29023 q ha hb
  have h8 (q : Pattern) (ha : d94259 q = 1) (hb : d116544 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94259, d116544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94259, d116544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94260 q = 1) (hb : d116545 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94260, d116545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94260, d116545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94261 q = 1) (hb : d116546 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94261, d116546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94261, d116546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94262 q = 1) (hb : d116547 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94262, d116547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94262, d116547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94263 q = 1) (hb : d116548 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94263, d116548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d94263, d116548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro29025 (p : Pattern) (ha : d94268 p = 1) (hb : d115756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8444 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8450 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8464 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d115751 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94264 q = 1) (hb : d115752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94264, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8481 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94265 q = 1) (hb : d115753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94265, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94266 q = 1) (hb : d115754 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94266, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94267 q = 1) (hb : d115755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94267, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94268 q = 1) (hb : d115756 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94268, d115756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94268, d115756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29026 (p : Pattern) (ha : d94273 p = 1) (hb : d115765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8450 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8464 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d115751 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94264 q = 1) (hb : d115752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94264, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8481 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94265 q = 1) (hb : d115753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94265, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94266 q = 1) (hb : d115754 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94266, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94267 q = 1) (hb : d115755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94267, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8490 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8494 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8497 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d115760 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94269 q = 1) (hb : d115761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d115761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94269, d115761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8503 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94270 q = 1) (hb : d115762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d115762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94270, d115762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94271 q = 1) (hb : d115763 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94271, d115763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94271, d115763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94272 q = 1) (hb : d115764 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94272, d115764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94272, d115764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94273 q = 1) (hb : d115765 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94273, d115765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94273, d115765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29027 (p : Pattern) (ha : d94280 p = 1) (hb : d116551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8497 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d115760 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94269 q = 1) (hb : d115761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d115761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94269, d115761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8503 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94270 q = 1) (hb : d115762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d115762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94270, d115762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94278 q = 1) (hb : d115763 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94278, d115763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94278, d115763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94279 q = 1) (hb : d115764 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94279, d115764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94279, d115764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94280 q = 1) (hb : d116551 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94280, d116551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94280, d116551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29028 (p : Pattern) (ha : d94290 p = 1) (hb : d116562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8540 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116557 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94286 q = 1) (hb : d116558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94286, d116558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94286, d116558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8557 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94287 q = 1) (hb : d116559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94287, d116559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94287, d116559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94288 q = 1) (hb : d116560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94288, d116560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94288, d116560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94289 q = 1) (hb : d116561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94289, d116561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94289, d116561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94290 q = 1) (hb : d116562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94290, d116562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94290, d116562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29029 (p : Pattern) (ha : d94296 p = 1) (hb : d116568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8438 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94274 q = 1) (hb : d115766 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94274, d115766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29025 q ha hb
    | true =>
      simp only [d94274, d115766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29026 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8515 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94275 q = 1) (hb : d115767 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94275, d115767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94275, d115767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94276 q = 1) (hb : d116549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94276, d116549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94276, d116549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94277 q = 1) (hb : d116550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94277, d116550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94277, d116550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94281 q = 1) (hb : d116552 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94281, d116552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94281, d116552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29027 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94282 q = 1) (hb : d116553 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94282, d116553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94282, d116553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94283 q = 1) (hb : d116554 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94283, d116554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94283, d116554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94284 q = 1) (hb : d116555 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94284, d116555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94284, d116555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94285 q = 1) (hb : d116556 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94285, d116556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94285, d116556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94291 q = 1) (hb : d116563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94291, d116563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94291, d116563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29028 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94292 q = 1) (hb : d116564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94292, d116564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94292, d116564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94293 q = 1) (hb : d116565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94293, d116565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94293, d116565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94294 q = 1) (hb : d116566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94294, d116566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94294, d116566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94295 q = 1) (hb : d116567 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94295, d116567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94295, d116567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94296 q = 1) (hb : d116568 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94296, d116568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94296, d116568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29030 (p : Pattern) (ha : d94302 p = 1) (hb : d116574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94297 q = 1) (hb : d116569 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94297, d116569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94297, d116569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29029 q ha hb
  have h2 (q : Pattern) (ha : d94298 q = 1) (hb : d116570 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94298, d116570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94298, d116570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94299 q = 1) (hb : d116571 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94299, d116571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94299, d116571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94300 q = 1) (hb : d116572 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94300, d116572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94300, d116572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94301 q = 1) (hb : d116573 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94301, d116573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94301, d116573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94302 q = 1) (hb : d116574 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94302, d116574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94302, d116574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29031 (p : Pattern) (ha : d94308 p = 1) (hb : d115887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8606 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8612 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8626 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d115882 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94304 q = 1) (hb : d115883 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d115883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94304, d115883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8643 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94305 q = 1) (hb : d115884 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d115884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94305, d115884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94306 q = 1) (hb : d115885 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d115885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94306, d115885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94307 q = 1) (hb : d115886 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d115886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94307, d115886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94308 q = 1) (hb : d115887 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94308, d115887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94308, d115887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29032 (p : Pattern) (ha : d94313 p = 1) (hb : d115896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8606 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8612 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d115882 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94304 q = 1) (hb : d115883 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d115883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94304, d115883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8643 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94305 q = 1) (hb : d115884 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d115884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94305, d115884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94306 q = 1) (hb : d115885 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d115885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94306, d115885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94307 q = 1) (hb : d115886 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d115886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94307, d115886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8652 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8656 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8659 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d115891 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94309 q = 1) (hb : d115892 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d115892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94309, d115892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8665 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94310 q = 1) (hb : d115893 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d115893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94310, d115893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94311 q = 1) (hb : d115894 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94311, d115894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94311, d115894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94312 q = 1) (hb : d115895 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94312, d115895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94312, d115895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94313 q = 1) (hb : d115896 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94313, d115896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94313, d115896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29033 (p : Pattern) (ha : d94320 p = 1) (hb : d116578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d115891 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94309 q = 1) (hb : d115892 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d115892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94309, d115892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8665 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94310 q = 1) (hb : d115893 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d115893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94310, d115893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94318 q = 1) (hb : d115894 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94318, d115894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94318, d115894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94319 q = 1) (hb : d115895 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94319, d115895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94319, d115895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94320 q = 1) (hb : d116578 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94320, d116578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94320, d116578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29034 (p : Pattern) (ha : d94330 p = 1) (hb : d116589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8702 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116584 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94326 q = 1) (hb : d116585 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94326, d116585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94326, d116585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8723 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94327 q = 1) (hb : d116586 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94327, d116586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94327, d116586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94328 q = 1) (hb : d116587 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94328, d116587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94328, d116587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94329 q = 1) (hb : d116588 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94329, d116588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94329, d116588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94330 q = 1) (hb : d116589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94330, d116589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94330, d116589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29035 (p : Pattern) (ha : d94336 p = 1) (hb : d116595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8600 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94314 q = 1) (hb : d115897 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94314, d115897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29031 q ha hb
    | true =>
      simp only [d94314, d115897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29032 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8677 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94315 q = 1) (hb : d115898 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94315, d115898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94315, d115898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94316 q = 1) (hb : d116576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94316, d116576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94316, d116576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94317 q = 1) (hb : d116577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94317, d116577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94317, d116577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94321 q = 1) (hb : d116579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94321, d116579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94321, d116579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29033 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94322 q = 1) (hb : d116580 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94322, d116580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94322, d116580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94323 q = 1) (hb : d116581 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94323, d116581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94323, d116581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94324 q = 1) (hb : d116582 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94324, d116582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94324, d116582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94325 q = 1) (hb : d116583 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94325, d116583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94325, d116583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94331 q = 1) (hb : d116590 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94331, d116590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94331, d116590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29034 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94332 q = 1) (hb : d116591 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94332, d116591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94332, d116591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94333 q = 1) (hb : d116592 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94333, d116592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94333, d116592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94334 q = 1) (hb : d116593 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94334, d116593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94334, d116593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94335 q = 1) (hb : d116594 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94335, d116594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94335, d116594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94336 q = 1) (hb : d116595 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94336, d116595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94336, d116595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29036 (p : Pattern) (ha : d94342 p = 1) (hb : d116601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94337 q = 1) (hb : d116596 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94337, d116596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94337, d116596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29035 q ha hb
  have h2 (q : Pattern) (ha : d94338 q = 1) (hb : d116597 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94338, d116597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94338, d116597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94339 q = 1) (hb : d116598 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94339, d116598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94339, d116598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94340 q = 1) (hb : d116599 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94340, d116599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94340, d116599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94341 q = 1) (hb : d116600 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94341, d116600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94341, d116600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94342 q = 1) (hb : d116601 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94342, d116601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94342, d116601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29037 (p : Pattern) (ha : d94349 p = 1) (hb : d116024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8793 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d116019 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94345 q = 1) (hb : d116020 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d116020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94345, d116020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8810 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94346 q = 1) (hb : d116021 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d116021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94346, d116021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94347 q = 1) (hb : d116022 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d116022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94347, d116022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94348 q = 1) (hb : d116023 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d116023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94348, d116023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94349 q = 1) (hb : d116024 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94349, d116024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94349, d116024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29038 (p : Pattern) (ha : d94354 p = 1) (hb : d116033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8793 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d116019 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94345 q = 1) (hb : d116020 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d116020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94345, d116020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8810 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94346 q = 1) (hb : d116021 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d116021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94346, d116021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94347 q = 1) (hb : d116022 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d116022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94347, d116022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94348 q = 1) (hb : d116023 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d116023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94348, d116023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8819 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8823 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8826 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116028 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94350 q = 1) (hb : d116029 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d116029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94350, d116029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8832 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94351 q = 1) (hb : d116030 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d116030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94351, d116030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94352 q = 1) (hb : d116031 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94352, d116031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94352, d116031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94353 q = 1) (hb : d116032 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94353, d116032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94353, d116032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94354 q = 1) (hb : d116033 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94354, d116033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94354, d116033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29039 (p : Pattern) (ha : d94361 p = 1) (hb : d116606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116028 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94350 q = 1) (hb : d116029 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d116029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94350, d116029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94351 q = 1) (hb : d116030 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d116030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94351, d116030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94359 q = 1) (hb : d116031 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94359, d116031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94359, d116031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94360 q = 1) (hb : d116032 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94360, d116032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94360, d116032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94361 q = 1) (hb : d116606 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94361, d116606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94361, d116606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29040 (p : Pattern) (ha : d94371 p = 1) (hb : d116621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8869 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116616 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94367 q = 1) (hb : d116617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94367, d116617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94367, d116617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8890 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94368 q = 1) (hb : d116618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94368, d116618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94368, d116618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94369 q = 1) (hb : d116619 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94369, d116619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94369, d116619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94370 q = 1) (hb : d116620 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94370, d116620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94370, d116620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94371 q = 1) (hb : d116621 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94371, d116621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94371, d116621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29041 (p : Pattern) (ha : d94377 p = 1) (hb : d116627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8767 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94355 q = 1) (hb : d116034 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94355, d116034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29037 q ha hb
    | true =>
      simp only [d94355, d116034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29038 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8844 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94356 q = 1) (hb : d116035 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94356, d116035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94356, d116035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94357 q = 1) (hb : d116604 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94357, d116604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94357, d116604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94358 q = 1) (hb : d116605 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94358, d116605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94358, d116605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94362 q = 1) (hb : d116607 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94362, d116607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94362, d116607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29039 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94363 q = 1) (hb : d116608 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94363, d116608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94363, d116608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94364 q = 1) (hb : d116609 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94364, d116609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94364, d116609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94365 q = 1) (hb : d116610 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94365, d116610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94365, d116610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94366 q = 1) (hb : d116611 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94366, d116611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94366, d116611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94372 q = 1) (hb : d116622 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94372, d116622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94372, d116622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29040 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94373 q = 1) (hb : d116623 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94373, d116623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94373, d116623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94374 q = 1) (hb : d116624 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94374, d116624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94374, d116624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94375 q = 1) (hb : d116625 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94375, d116625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94375, d116625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94376 q = 1) (hb : d116626 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94376, d116626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94376, d116626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94377 q = 1) (hb : d116627 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94377, d116627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94377, d116627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29042 (p : Pattern) (ha : d94383 p = 1) (hb : d116633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94378 q = 1) (hb : d116628 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94378, d116628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94378, d116628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29041 q ha hb
  have h2 (q : Pattern) (ha : d94379 q = 1) (hb : d116629 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94379, d116629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94379, d116629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94380 q = 1) (hb : d116630 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94380, d116630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94380, d116630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94381 q = 1) (hb : d116631 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94381, d116631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94381, d116631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94382 q = 1) (hb : d116632 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94382, d116632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94382, d116632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94383 q = 1) (hb : d116633 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94383, d116633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94383, d116633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29043 (p : Pattern) (ha : d94391 p = 1) (hb : d116180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8941 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8947 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8961 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d116175 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94387 q = 1) (hb : d116176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d116176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94387, d116176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8978 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94388 q = 1) (hb : d116177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d116177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94388, d116177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94389 q = 1) (hb : d116178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d116178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94389, d116178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94390 q = 1) (hb : d116179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d116179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94390, d116179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94391 q = 1) (hb : d116180 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94391, d116180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94391, d116180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29044 (p : Pattern) (ha : d94396 p = 1) (hb : d116189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8947 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8961 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d116175 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94387 q = 1) (hb : d116176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d116176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94387, d116176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8978 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94388 q = 1) (hb : d116177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d116177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94388, d116177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94389 q = 1) (hb : d116178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d116178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94389, d116178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94390 q = 1) (hb : d116179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d116179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94390, d116179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8987 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8991 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8994 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116184 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94392 q = 1) (hb : d116185 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d116185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94392, d116185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9000 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94393 q = 1) (hb : d116186 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d116186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94393, d116186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94394 q = 1) (hb : d116187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94394, d116187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94394, d116187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94395 q = 1) (hb : d116188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94395, d116188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94395, d116188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94396 q = 1) (hb : d116189 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94396, d116189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94396, d116189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29045 (p : Pattern) (ha : d94403 p = 1) (hb : d116639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116184 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94392 q = 1) (hb : d116185 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d116185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94392, d116185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9000 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94393 q = 1) (hb : d116186 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d116186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94393, d116186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94401 q = 1) (hb : d116187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94401, d116187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94401, d116187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94402 q = 1) (hb : d116188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94402, d116188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94402, d116188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94403 q = 1) (hb : d116639 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94403, d116639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94403, d116639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29046 (p : Pattern) (ha : d94413 p = 1) (hb : d116654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9037 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116649 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94409 q = 1) (hb : d116650 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94409, d116650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94409, d116650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9058 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94410 q = 1) (hb : d116651 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94410, d116651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94410, d116651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94411 q = 1) (hb : d116652 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94411, d116652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94411, d116652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94412 q = 1) (hb : d116653 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94412, d116653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94412, d116653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94413 q = 1) (hb : d116654 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94413, d116654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94413, d116654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29047 (p : Pattern) (ha : d94419 p = 1) (hb : d116660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94397 q = 1) (hb : d116190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94397, d116190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29043 q ha hb
    | true =>
      simp only [d94397, d116190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29044 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94398 q = 1) (hb : d116191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94398, d116191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94398, d116191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94399 q = 1) (hb : d116637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94399, d116637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94399, d116637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94400 q = 1) (hb : d116638 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94400, d116638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94400, d116638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94404 q = 1) (hb : d116640 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94404, d116640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94404, d116640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29045 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94405 q = 1) (hb : d116641 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94405, d116641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94405, d116641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94406 q = 1) (hb : d116642 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94406, d116642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94406, d116642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94407 q = 1) (hb : d116643 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94407, d116643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94407, d116643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94408 q = 1) (hb : d116644 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94408, d116644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94408, d116644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94414 q = 1) (hb : d116655 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94414, d116655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94414, d116655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29046 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94415 q = 1) (hb : d116656 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94415, d116656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94415, d116656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94416 q = 1) (hb : d116657 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94416, d116657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94416, d116657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94417 q = 1) (hb : d116658 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94417, d116658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94417, d116658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94418 q = 1) (hb : d116659 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94418, d116659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94418, d116659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94419 q = 1) (hb : d116660 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94419, d116660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94419, d116660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29048 (p : Pattern) (ha : d94425 p = 1) (hb : d116666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94420 q = 1) (hb : d116661 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94420, d116661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94420, d116661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29047 q ha hb
  have h2 (q : Pattern) (ha : d94421 q = 1) (hb : d116662 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94421, d116662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94421, d116662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94422 q = 1) (hb : d116663 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94422, d116663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94422, d116663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94423 q = 1) (hb : d116664 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94423, d116664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94423, d116664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94424 q = 1) (hb : d116665 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94424, d116665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94424, d116665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94425 q = 1) (hb : d116666 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94425, d116666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94425, d116666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29049 (p : Pattern) (ha : d94434 p = 1) (hb : d116337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9116 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d9130 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d116332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94430 q = 1) (hb : d116333 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d116333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94430, d116333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94431 q = 1) (hb : d116334 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d116334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94431, d116334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94432 q = 1) (hb : d116335 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d116335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94432, d116335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94433 q = 1) (hb : d116336 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d116336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94433, d116336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94434 q = 1) (hb : d116337 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94434, d116337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94434, d116337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29050 (p : Pattern) (ha : d94439 p = 1) (hb : d116346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9110 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9116 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d116332 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94430 q = 1) (hb : d116333 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d116333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94430, d116333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9147 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94431 q = 1) (hb : d116334 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d116334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94431, d116334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94432 q = 1) (hb : d116335 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d116335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94432, d116335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94433 q = 1) (hb : d116336 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d116336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94433, d116336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9156 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d9160 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d9163 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116341 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94435 q = 1) (hb : d116342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d116342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94435, d116342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9169 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94436 q = 1) (hb : d116343 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d116343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94436, d116343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94437 q = 1) (hb : d116344 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94437, d116344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94437, d116344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94438 q = 1) (hb : d116345 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94438, d116345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94438, d116345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94439 q = 1) (hb : d116346 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94439, d116346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94439, d116346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro29051 (p : Pattern) (ha : d94446 p = 1) (hb : d116673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9163 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116341 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94435 q = 1) (hb : d116342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d116342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94435, d116342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9169 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94436 q = 1) (hb : d116343 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d116343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94436, d116343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94444 q = 1) (hb : d116344 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94444, d116344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94444, d116344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94445 q = 1) (hb : d116345 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94445, d116345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94445, d116345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94446 q = 1) (hb : d116673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94446, d116673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94446, d116673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29052 (p : Pattern) (ha : d94456 p = 1) (hb : d116688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9206 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94452 q = 1) (hb : d116684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94452, d116684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94452, d116684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9227 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94453 q = 1) (hb : d116685 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94453, d116685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94453, d116685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94454 q = 1) (hb : d116686 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94454, d116686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94454, d116686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94455 q = 1) (hb : d116687 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94455, d116687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94455, d116687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94456 q = 1) (hb : d116688 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94456, d116688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94456, d116688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29053 (p : Pattern) (ha : d94462 p = 1) (hb : d116694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9104 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94440 q = 1) (hb : d116347 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94440, d116347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29049 q ha hb
    | true =>
      simp only [d94440, d116347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29050 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94441 q = 1) (hb : d116348 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94441, d116348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94441, d116348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94442 q = 1) (hb : d116671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94442, d116671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94442, d116671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94443 q = 1) (hb : d116672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94443, d116672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94443, d116672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94447 q = 1) (hb : d116674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94447, d116674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94447, d116674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29051 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94448 q = 1) (hb : d116675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94448, d116675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94448, d116675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94449 q = 1) (hb : d116676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94449, d116676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94449, d116676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94450 q = 1) (hb : d116677 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94450, d116677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94450, d116677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94451 q = 1) (hb : d116678 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94451, d116678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94451, d116678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94457 q = 1) (hb : d116689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94457, d116689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94457, d116689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29052 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94458 q = 1) (hb : d116690 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94458, d116690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94458, d116690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94459 q = 1) (hb : d116691 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94459, d116691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94459, d116691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94460 q = 1) (hb : d116692 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94460, d116692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94460, d116692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94461 q = 1) (hb : d116693 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94461, d116693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94461, d116693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94462 q = 1) (hb : d116694 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94462, d116694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94462, d116694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29054 (p : Pattern) (ha : d94468 p = 1) (hb : d116700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94463 q = 1) (hb : d116695 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94463, d116695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94463, d116695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29053 q ha hb
  have h2 (q : Pattern) (ha : d94464 q = 1) (hb : d116696 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94464, d116696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94464, d116696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94465 q = 1) (hb : d116697 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94465, d116697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94465, d116697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94466 q = 1) (hb : d116698 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94466, d116698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94466, d116698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94467 q = 1) (hb : d116699 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94467, d116699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94467, d116699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94468 q = 1) (hb : d116700 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94468, d116700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94468, d116700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29055 (p : Pattern) (ha : d94474 p = 1) (hb : d116706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d94303 q = 1) (hb : d116575 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94303, d116575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29024 q ha hb
    | true =>
      simp only [d94303, d116575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29030 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94343 q = 1) (hb : d116602 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94343, d116602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94343, d116602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29036 q ha hb
  have h3 (q : Pattern) (ha : d94344 q = 1) (hb : d116603 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94344, d116603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94344, d116603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94384 q = 1) (hb : d116634 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94384, d116634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94384, d116634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29042 q ha hb
  have h5 (q : Pattern) (ha : d94385 q = 1) (hb : d116635 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94385, d116635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94385, d116635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94386 q = 1) (hb : d116636 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94386, d116636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94386, d116636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94426 q = 1) (hb : d116667 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94426, d116667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94426, d116667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29048 q ha hb
  have h8 (q : Pattern) (ha : d94427 q = 1) (hb : d116668 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94427, d116668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94427, d116668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94428 q = 1) (hb : d116669 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94428, d116669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94428, d116669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94429 q = 1) (hb : d116670 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94429, d116670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94429, d116670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94469 q = 1) (hb : d116701 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94469, d116701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94469, d116701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29054 q ha hb
  have h12 (q : Pattern) (ha : d94470 q = 1) (hb : d116702 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94470, d116702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94470, d116702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94471 q = 1) (hb : d116703 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94471, d116703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94471, d116703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94472 q = 1) (hb : d116704 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94472, d116704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94472, d116704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94473 q = 1) (hb : d116705 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94473, d116705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94473, d116705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94474 q = 1) (hb : d116706 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94474, d116706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94474, d116706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro29056 (p : Pattern) (ha : d94480 p = 1) (hb : d116712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94475 q = 1) (hb : d116707 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94475, d116707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29055 q ha hb
    | true =>
      simp only [d94475, d116707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94476 q = 1) (hb : d116708 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94476, d116708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94476, d116708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94477 q = 1) (hb : d116709 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94477, d116709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94477, d116709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94478 q = 1) (hb : d116710 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94478, d116710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94478, d116710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94479 q = 1) (hb : d116711 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94479, d116711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94479, d116711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94480 q = 1) (hb : d116712 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94480, d116712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94480, d116712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29057 (p : Pattern) (ha : d94486 p = 1) (hb : d116718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94481 q = 1) (hb : d116713 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94481, d116713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29056 q ha hb
    | true =>
      simp only [d94481, d116713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94482 q = 1) (hb : d116714 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94482, d116714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94482, d116714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94483 q = 1) (hb : d116715 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94483, d116715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94483, d116715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94484 q = 1) (hb : d116716 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94484, d116716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94484, d116716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94485 q = 1) (hb : d116717 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94485, d116717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94485, d116717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94486 q = 1) (hb : d116718 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94486, d116718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94486, d116718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29058 (p : Pattern) (ha : d94492 p = 1) (hb : d116724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94487 q = 1) (hb : d116719 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94487, d116719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29057 q ha hb
    | true =>
      simp only [d94487, d116719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94488 q = 1) (hb : d116720 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94488, d116720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94488, d116720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94489 q = 1) (hb : d116721 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94489, d116721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94489, d116721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94490 q = 1) (hb : d116722 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94490, d116722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94490, d116722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94491 q = 1) (hb : d116723 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94491, d116723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94491, d116723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94492 q = 1) (hb : d116724 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94492, d116724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94492, d116724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29059 (p : Pattern) (ha : d94498 p = 1) (hb : d116730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94493 q = 1) (hb : d116725 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94493, d116725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29058 q ha hb
    | true =>
      simp only [d94493, d116725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94494 q = 1) (hb : d116726 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94494, d116726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94494, d116726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94495 q = 1) (hb : d116727 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94495, d116727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94495, d116727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94496 q = 1) (hb : d116728 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94496, d116728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94496, d116728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94497 q = 1) (hb : d116729 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94497, d116729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94497, d116729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94498 q = 1) (hb : d116730 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94498, d116730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94498, d116730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29060 (p : Pattern) (ha : d94504 p = 1) (hb : d116736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94499 q = 1) (hb : d116731 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94499, d116731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29059 q ha hb
    | true =>
      simp only [d94499, d116731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94500 q = 1) (hb : d116732 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94500, d116732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94500, d116732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94501 q = 1) (hb : d116733 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94501, d116733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94501, d116733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94502 q = 1) (hb : d116734 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94502, d116734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94502, d116734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94503 q = 1) (hb : d116735 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94503, d116735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94503, d116735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94504 q = 1) (hb : d116736 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94504, d116736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94504, d116736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29061 (p : Pattern) (ha : d94510 p = 1) (hb : d116742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94505 q = 1) (hb : d116737 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94505, d116737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29060 q ha hb
    | true =>
      simp only [d94505, d116737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94506 q = 1) (hb : d116738 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94506, d116738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94506, d116738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94507 q = 1) (hb : d116739 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94507, d116739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94507, d116739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94508 q = 1) (hb : d116740 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94508, d116740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94508, d116740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94509 q = 1) (hb : d116741 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94509, d116741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94509, d116741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94510 q = 1) (hb : d116742 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94510, d116742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94510, d116742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29062 (p : Pattern) (ha : d94516 p = 1) (hb : d116748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94511 q = 1) (hb : d116743 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94511, d116743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29061 q ha hb
    | true =>
      simp only [d94511, d116743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94512 q = 1) (hb : d116744 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94512, d116744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94512, d116744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94513 q = 1) (hb : d116745 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94513, d116745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94513, d116745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94514 q = 1) (hb : d116746 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94514, d116746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94514, d116746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94515 q = 1) (hb : d116747 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94515, d116747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94515, d116747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94516 q = 1) (hb : d116748 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94516, d116748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94516, d116748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29063 (p : Pattern) (ha : d12227 p = 1) (hb : d94755 p = 1) : d97457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d4821 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33 q = 1) (hb : d94753 q = 1) : d33 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12225 q = 1) (hb : d94755 q = 1) : d97455 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d94755, d97455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12225, d94755, d97455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d34 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d34, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12226 q = 1) (hb : d94755 q = 1) : d97456 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12226, d97456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12226, d97456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12227 q = 1) (hb : d94755 q = 1) : d97457 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12227, d97457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12227, d97457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29064 (p : Pattern) (ha : d12233 p = 1) (hb : d94755 p = 1) : d97463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d94755 q = 1) : d97458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29063 q ha hb
    | true =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d94755 q = 1) : d97459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12388 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d94755 q = 1) : d97460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d94755 q = 1) : d97461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12232 q = 1) (hb : d94755 q = 1) : d97462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d97462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12232, d97462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12233 q = 1) (hb : d94755 q = 1) : d97463 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12233, d97463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12233, d97463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29065 (p : Pattern) (ha : d94755 p = 1) (hb : d115242 p = 1) : d97469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12407 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12408 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12234 q = 1) (hb : d94755 q = 1) : d97464 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29064 q ha hb
    | true =>
      simp only [d12234, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12389 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115238 q = 1) : d97465 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115238, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12389 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115239 q = 1) : d97466 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d97466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115239, d97466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115240 q = 1) : d97467 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d97467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115240, d97467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115241 q = 1) : d97468 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d97468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115241, d97468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115242 q = 1) : d97469 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115242, d97469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115242, d97469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29066 (p : Pattern) (ha : d12240 p = 1) (hb : d94755 p = 1) : d97470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d94755 q = 1) : d97458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29063 q ha hb
    | true =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d94755 q = 1) : d97459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12388 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d94755 q = 1) : d97460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d94755 q = 1) : d97461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12232 q = 1) (hb : d94755 q = 1) : d97462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d97462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12232, d97462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12240 q = 1) (hb : d94755 q = 1) : d97470 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12240, d97470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12240, d97470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29067 (p : Pattern) (ha : d94755 p = 1) (hb : d115247 p = 1) : d97476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12407 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12408 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12234 q = 1) (hb : d94755 q = 1) : d97464 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29064 q ha hb
    | true =>
      simp only [d12234, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12389 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115238 q = 1) : d97465 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115238, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12389 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115239 q = 1) : d97466 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d97466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115239, d97466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115240 q = 1) : d97467 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d97467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115240, d97467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115241 q = 1) : d97468 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d97468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115241, d97468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12411 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12412 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12241 q = 1) (hb : d94755 q = 1) : d97471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29066 q ha hb
    | true =>
      simp only [d12241, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12391 q ha hb
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115243 q = 1) : d97472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d115243, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12391 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94755 q = 1) (hb : d115244 q = 1) : d97473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d97473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115244, d97473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d94755 q = 1) (hb : d115245 q = 1) : d97474 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115245, d97474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115245, d97474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94755 q = 1) (hb : d115246 q = 1) : d97475 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115246, d97475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d115246, d97475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94755 q = 1) (hb : d115247 q = 1) : d97476 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115247, d97476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115247, d97476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro29068 (p : Pattern) (ha : d94755 p = 1) (hb : d115254 p = 1) : d97481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12241 q = 1) (hb : d94755 q = 1) : d97471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29066 q ha hb
    | true =>
      simp only [d12241, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12391 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115243 q = 1) : d97472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115243, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12391 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115244 q = 1) : d97473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d97473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115244, d97473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115252 q = 1) : d97474 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115252, d97474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115252, d97474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115253 q = 1) : d97475 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115253, d97475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115253, d97475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115254 q = 1) : d97481 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115254, d97481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115254, d97481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29069 (p : Pattern) (ha : d12261 p = 1) (hb : d94755 p = 1) : d97489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6081 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74 q = 1) (hb : d94753 q = 1) : d74 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12259 q = 1) (hb : d94755 q = 1) : d97487 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d94755, d97487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12259, d94755, d97487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d74 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12260 q = 1) (hb : d94755 q = 1) : d97488 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12260, d97488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12260, d97488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12261 q = 1) (hb : d94755 q = 1) : d97489 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12261, d97489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12261, d97489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29070 (p : Pattern) (ha : d12267 p = 1) (hb : d94755 p = 1) : d97495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d94755 q = 1) : d97490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d97490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29069 q ha hb
    | true =>
      simp only [d12262, d97490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d94755 q = 1) : d97491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d97491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d97491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12394 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12264 q = 1) (hb : d94755 q = 1) : d97492 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12264, d97492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12264, d97492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12265 q = 1) (hb : d94755 q = 1) : d97493 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12265, d97493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12265, d97493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12266 q = 1) (hb : d94755 q = 1) : d97494 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12266, d97494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12266, d97494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12267 q = 1) (hb : d94755 q = 1) : d97495 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12267, d97495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12267, d97495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29071 (p : Pattern) (ha : d94755 p = 1) (hb : d115264 p = 1) : d97501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12268 q = 1) (hb : d94755 q = 1) : d97496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29070 q ha hb
    | true =>
      simp only [d12268, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12395 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115260 q = 1) : d97497 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115260, d97497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115260, d97497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12395 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115261 q = 1) : d97498 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115261, d97498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115261, d97498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115262 q = 1) : d97499 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115262, d97499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115262, d97499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115263 q = 1) : d97500 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115263, d97500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115263, d97500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115264 q = 1) : d97501 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115264, d97501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115264, d97501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29072 (p : Pattern) (ha : d94755 p = 1) (hb : d115270 p = 1) : d97507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12398 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12398 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12399 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115248 q = 1) : d97477 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115248, d97477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29065 q ha hb
    | true =>
      simp only [d115248, d97477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29067 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12400 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115249 q = 1) : d97478 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115249, d97478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115249, d97478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115250 q = 1) : d97479 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115250, d97479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115250, d97479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d115251 q = 1) : d97480 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115251, d97480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115251, d97480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d115255 q = 1) : d97482 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115255, d97482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115255, d97482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29068 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115256 q = 1) : d97483 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115256, d97483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115256, d97483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115257 q = 1) : d97484 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115257, d97484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115257, d97484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115258 q = 1) : d97485 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115258, d97485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115258, d97485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115259 q = 1) : d97486 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115259, d97486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115259, d97486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94755 q = 1) (hb : d115265 q = 1) : d97502 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115265, d97502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115265, d97502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29071 q ha hb
  have h17 (q : Pattern) (ha : d94755 q = 1) (hb : d115266 q = 1) : d97503 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115266, d97503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115266, d97503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d94755 q = 1) (hb : d115267 q = 1) : d97504 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115267, d97504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115267, d97504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d94755 q = 1) (hb : d115268 q = 1) : d97505 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115268, d97505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115268, d97505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d94755 q = 1) (hb : d115269 q = 1) : d97506 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115269, d97506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115269, d97506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d94755 q = 1) (hb : d115270 q = 1) : d97507 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115270, d97507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115270, d97507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro29073 (p : Pattern) (ha : d12289 p = 1) (hb : d94755 p = 1) : d97517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d94755 q = 1) : d97464 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29064 q ha hb
    | true =>
      simp only [d12234, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12389 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d94755 q = 1) : d97513 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d94755 q = 1) : d97514 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d94755 q = 1) : d97515 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d94755 q = 1) : d97516 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12289 q = 1) (hb : d94755 q = 1) : d97517 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d97517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d97517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29074 (p : Pattern) (ha : d12296 p = 1) (hb : d94755 p = 1) : d97524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d94755 q = 1) : d97464 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29064 q ha hb
    | true =>
      simp only [d12234, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12389 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d94755 q = 1) : d97513 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d94755 q = 1) : d97514 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d94755 q = 1) : d97515 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d94755 q = 1) : d97516 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12241 q = 1) (hb : d94755 q = 1) : d97471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29066 q ha hb
    | true =>
      simp only [d12241, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12391 q ha hb
  have h7 (q : Pattern) (ha : d12292 q = 1) (hb : d94755 q = 1) : d97520 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d97520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d97520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12293 q = 1) (hb : d94755 q = 1) : d97521 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d97521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12293, d97521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12294 q = 1) (hb : d94755 q = 1) : d97522 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d97522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d97522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12295 q = 1) (hb : d94755 q = 1) : d97523 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d97523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d97523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12296 q = 1) (hb : d94755 q = 1) : d97524 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d97524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12296, d97524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29075 (p : Pattern) (ha : d12373 p = 1) (hb : d94755 p = 1) : d97572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d94755 q = 1) : d97464 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29064 q ha hb
    | true =>
      simp only [d12234, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12389 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d94755 q = 1) : d97513 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d94755 q = 1) : d97514 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d94755 q = 1) : d97515 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d94755 q = 1) : d97516 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12389 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12373 q = 1) (hb : d94755 q = 1) : d97572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12373, d97572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12373, d97572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29076 (p : Pattern) (ha : d12301 p = 1) (hb : d94755 p = 1) : d97529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d94755 q = 1) : d97458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29063 q ha hb
    | true =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d94755 q = 1) : d97459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12388 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d94755 q = 1) : d97460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d94755 q = 1) : d97461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12300 q = 1) (hb : d94755 q = 1) : d97528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d97528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d97528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12301 q = 1) (hb : d94755 q = 1) : d97529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12301, d97529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12301, d97529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29077 (p : Pattern) (ha : d12308 p = 1) (hb : d94755 p = 1) : d97536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d94755 q = 1) : d97458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29063 q ha hb
    | true =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d94755 q = 1) : d97459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12388 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d94755 q = 1) : d97460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12306 q = 1) (hb : d94755 q = 1) : d97534 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d97534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d97534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12307 q = 1) (hb : d94755 q = 1) : d97535 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d97535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12307, d97535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12308 q = 1) (hb : d94755 q = 1) : d97536 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12308, d97536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12308, d97536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29078 (p : Pattern) (ha : d12318 p = 1) (hb : d94755 p = 1) : d97542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4821 q = 1) (hb : d94753 q = 1) : d4821 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12316 q = 1) (hb : d94755 q = 1) : d97540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d94755, d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12316, d94755, d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4821 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33 q = 1) (hb : d94753 q = 1) : d33 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12225 q = 1) (hb : d94755 q = 1) : d97455 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d94755, d97455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d12225, d94755, d97455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12317 q = 1) (hb : d94755 q = 1) : d97541 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12317, d97541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12317, d97541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12318 q = 1) (hb : d94755 q = 1) : d97542 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12318, d97542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12318, d97542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29079 (p : Pattern) (ha : d12324 p = 1) (hb : d94755 p = 1) : d150555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d94755 q = 1) : d97543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d97543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29078 q ha hb
    | true =>
      simp only [d12319, d97543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d94755 q = 1) : d97544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d97544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d97544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d94755 q = 1) : d97458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29063 q ha hb
    | true =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d94755 q = 1) : d97459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d94755 q = 1) : d150552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d150552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d150552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d94755 q = 1) : d150553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d150553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d150553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d94755 q = 1) : d150554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d150554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d150554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12324 q = 1) (hb : d94755 q = 1) : d150555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12324, d150555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12324, d150555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29080 (p : Pattern) (ha : d12344 p = 1) (hb : d94755 p = 1) : d97463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d94755 q = 1) : d97458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29063 q ha hb
    | true =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d94755 q = 1) : d97459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d94755 q = 1) : d97460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d94755 q = 1) : d97461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d94755 q = 1) : d97462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d97462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d97462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12344 q = 1) (hb : d94755 q = 1) : d97463 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12344, d97463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12344, d97463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29081 (p : Pattern) (ha : d94755 p = 1) (hb : d115280 p = 1) : d150561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12302 q = 1) (hb : d94755 q = 1) : d97530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d97530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29076 q ha hb
    | true =>
      simp only [d12302, d97530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12407 q ha hb
  have h2 (q : Pattern) (ha : d12303 q = 1) (hb : d94755 q = 1) : d97531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d97531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d97531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12304 q = 1) (hb : d94755 q = 1) : d97532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d97532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12304, d97532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12305 q = 1) (hb : d94755 q = 1) : d97533 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d97533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d97533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12309 q = 1) (hb : d94755 q = 1) : d97537 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d97537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29077 q ha hb
    | true =>
      simp only [d12309, d97537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12408 q ha hb
  have h6 (q : Pattern) (ha : d12310 q = 1) (hb : d94755 q = 1) : d97538 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d97538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d97538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12311 q = 1) (hb : d94755 q = 1) : d97539 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d97539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12311, d97539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12325 q = 1) (hb : d94755 q = 1) : d150556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d150556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29079 q ha hb
    | true =>
      simp only [d12325, d150556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29064 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115276 q = 1) : d150557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d150557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115276, d150557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d12345 q = 1) (hb : d94755 q = 1) : d97464 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29080 q ha hb
    | true =>
      simp only [d12345, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12346 q = 1) (hb : d94755 q = 1) : d97465 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12346, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115277 q = 1) : d150558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d150558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115277, d150558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115278 q = 1) : d150559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d150559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115278, d150559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115279 q = 1) : d150560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d150560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115279, d150560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115280 q = 1) : d150561 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115280, d150561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115280, d150561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29082 (p : Pattern) (ha : d12351 p = 1) (hb : d94755 p = 1) : d97555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d94755 q = 1) : d97458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29063 q ha hb
    | true =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d94755 q = 1) : d97459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12388 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d94755 q = 1) : d97460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d94755 q = 1) : d97461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12300 q = 1) (hb : d94755 q = 1) : d97528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d97528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d97528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12351 q = 1) (hb : d94755 q = 1) : d97555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12351, d97555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12351, d97555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29083 (p : Pattern) (ha : d12356 p = 1) (hb : d94755 p = 1) : d97560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d94755 q = 1) : d97458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29063 q ha hb
    | true =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d94755 q = 1) : d97459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12388 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d94755 q = 1) : d97460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12306 q = 1) (hb : d94755 q = 1) : d97534 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d97534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d97534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12307 q = 1) (hb : d94755 q = 1) : d97535 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d97535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12307, d97535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12356 q = 1) (hb : d94755 q = 1) : d97560 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12356, d97560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12356, d97560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29084 (p : Pattern) (ha : d12360 p = 1) (hb : d94755 p = 1) : d150562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d94755 q = 1) : d97543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d97543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29078 q ha hb
    | true =>
      simp only [d12319, d97543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d94755 q = 1) : d97544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d97544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d97544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d94755 q = 1) : d97458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29063 q ha hb
    | true =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d94755 q = 1) : d97459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d94755 q = 1) : d150552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d150552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d150552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d94755 q = 1) : d150553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d150553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d150553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d94755 q = 1) : d150554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d150554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d150554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12360 q = 1) (hb : d94755 q = 1) : d150562 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12360, d150562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12360, d150562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29085 (p : Pattern) (ha : d12365 p = 1) (hb : d94755 p = 1) : d97470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d94755 q = 1) : d97458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29063 q ha hb
    | true =>
      simp only [d12228, d97458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d94755 q = 1) : d97459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d97459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d94755 q = 1) : d97460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d97460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d94755 q = 1) : d97461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d97461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d94755 q = 1) : d97462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d97462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d97462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12365 q = 1) (hb : d94755 q = 1) : d97470 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12365, d97470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12365, d97470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29086 (p : Pattern) (ha : d94755 p = 1) (hb : d115285 p = 1) : d150568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12302 q = 1) (hb : d94755 q = 1) : d97530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d97530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29076 q ha hb
    | true =>
      simp only [d12302, d97530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12407 q ha hb
  have h2 (q : Pattern) (ha : d12303 q = 1) (hb : d94755 q = 1) : d97531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d97531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d97531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12304 q = 1) (hb : d94755 q = 1) : d97532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d97532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12304, d97532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12305 q = 1) (hb : d94755 q = 1) : d97533 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d97533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d97533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12309 q = 1) (hb : d94755 q = 1) : d97537 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d97537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29077 q ha hb
    | true =>
      simp only [d12309, d97537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12408 q ha hb
  have h6 (q : Pattern) (ha : d12310 q = 1) (hb : d94755 q = 1) : d97538 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d97538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d97538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12311 q = 1) (hb : d94755 q = 1) : d97539 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d97539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12311, d97539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12325 q = 1) (hb : d94755 q = 1) : d150556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d150556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29079 q ha hb
    | true =>
      simp only [d12325, d150556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29064 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115276 q = 1) : d150557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d150557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115276, d150557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d12345 q = 1) (hb : d94755 q = 1) : d97464 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29080 q ha hb
    | true =>
      simp only [d12345, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12346 q = 1) (hb : d94755 q = 1) : d97465 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12346, d97465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115277 q = 1) : d150558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d150558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115277, d150558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115278 q = 1) : d150559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d150559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115278, d150559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115279 q = 1) : d150560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d150560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115279, d150560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12352 q = 1) (hb : d94755 q = 1) : d97556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12352, d97556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29082 q ha hb
    | true =>
      simp only [d12352, d97556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12411 q ha hb
  have h16 (q : Pattern) (ha : d12353 q = 1) (hb : d94755 q = 1) : d97557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12353, d97557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12353, d97557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12354 q = 1) (hb : d94755 q = 1) : d97558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12354, d97558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12354, d97558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12355 q = 1) (hb : d94755 q = 1) : d97559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12355, d97559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12355, d97559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12357 q = 1) (hb : d94755 q = 1) : d97561 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12357, d97561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29083 q ha hb
    | true =>
      simp only [d12357, d97561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12412 q ha hb
  have h20 (q : Pattern) (ha : d12358 q = 1) (hb : d94755 q = 1) : d97562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12358, d97562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12358, d97562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12359 q = 1) (hb : d94755 q = 1) : d97563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12359, d97563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12359, d97563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12361 q = 1) (hb : d94755 q = 1) : d150563 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d150563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29084 q ha hb
    | true =>
      simp only [d12361, d150563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29066 q ha hb
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115281 q = 1) : d150564 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d150564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d115281, d150564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d12366 q = 1) (hb : d94755 q = 1) : d97471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29085 q ha hb
    | true =>
      simp only [d12366, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12367 q = 1) (hb : d94755 q = 1) : d97472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12367, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94755 q = 1) (hb : d115282 q = 1) : d150565 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d150565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115282, d150565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d94755 q = 1) (hb : d115283 q = 1) : d150566 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115283, d150566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115283, d150566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94755 q = 1) (hb : d115284 q = 1) : d150567 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115284, d150567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d115284, d150567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94755 q = 1) (hb : d115285 q = 1) : d150568 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115285, d150568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115285, d150568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro29087 (p : Pattern) (ha : d94755 p = 1) (hb : d115292 p = 1) : d150575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12361 q = 1) (hb : d94755 q = 1) : d150563 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d150563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29084 q ha hb
    | true =>
      simp only [d12361, d150563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29066 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115281 q = 1) : d150564 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d150564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115281, d150564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12366 q = 1) (hb : d94755 q = 1) : d97471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29085 q ha hb
    | true =>
      simp only [d12366, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12367 q = 1) (hb : d94755 q = 1) : d97472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12367, d97472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115282 q = 1) : d150565 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d150565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115282, d150565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115290 q = 1) : d150573 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115290, d150573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115290, d150573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115291 q = 1) : d150574 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115291, d150574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115291, d150574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115292 q = 1) : d150575 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115292, d150575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115292, d150575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29088 (p : Pattern) (ha : d12392 p = 1) (hb : d94755 p = 1) : d97587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6081 q = 1) (hb : d94753 q = 1) : d6081 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12390 q = 1) (hb : d94755 q = 1) : d97585 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d94755, d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12390, d94755, d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6081 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74 q = 1) (hb : d94753 q = 1) : d74 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12259 q = 1) (hb : d94755 q = 1) : d97487 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d94755, d97487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d12259, d94755, d97487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12391 q = 1) (hb : d94755 q = 1) : d97586 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12391, d97586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12391, d97586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12392 q = 1) (hb : d94755 q = 1) : d97587 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12392, d97587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12392, d97587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29089 (p : Pattern) (ha : d12398 p = 1) (hb : d94755 p = 1) : d150584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12393 q = 1) (hb : d94755 q = 1) : d97588 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12393, d97588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29088 q ha hb
    | true =>
      simp only [d12393, d97588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12394 q = 1) (hb : d94755 q = 1) : d97589 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12394, d97589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12394, d97589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12262 q = 1) (hb : d94755 q = 1) : d97490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d97490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29069 q ha hb
    | true =>
      simp only [d12262, d97490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12263 q = 1) (hb : d94755 q = 1) : d97491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d97491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d97491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12395 q = 1) (hb : d94755 q = 1) : d150581 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12395, d150581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12395, d150581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12396 q = 1) (hb : d94755 q = 1) : d150582 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12396, d150582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12396, d150582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12397 q = 1) (hb : d94755 q = 1) : d150583 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12397, d150583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12397, d150583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12398 q = 1) (hb : d94755 q = 1) : d150584 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12398, d150584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12398, d150584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29090 (p : Pattern) (ha : d12418 p = 1) (hb : d94755 p = 1) : d97495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d94755 q = 1) : d97490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d97490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29069 q ha hb
    | true =>
      simp only [d12262, d97490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d94755 q = 1) : d97491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d97491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d97491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12415 q = 1) (hb : d94755 q = 1) : d97492 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12415, d97492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12415, d97492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12416 q = 1) (hb : d94755 q = 1) : d97493 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12416, d97493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12416, d97493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12417 q = 1) (hb : d94755 q = 1) : d97494 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12417, d97494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12417, d97494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12418 q = 1) (hb : d94755 q = 1) : d97495 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12418, d97495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12418, d97495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29091 (p : Pattern) (ha : d94755 p = 1) (hb : d115302 p = 1) : d150590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12399 q = 1) (hb : d94755 q = 1) : d150585 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12399, d150585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29089 q ha hb
    | true =>
      simp only [d12399, d150585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29070 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115298 q = 1) : d150586 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115298, d150586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115298, d150586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12419 q = 1) (hb : d94755 q = 1) : d97496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12419, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29090 q ha hb
    | true =>
      simp only [d12419, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12420 q = 1) (hb : d94755 q = 1) : d97497 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12420, d97497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12420, d97497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115299 q = 1) : d150587 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115299, d150587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115299, d150587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115300 q = 1) : d150588 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115300, d150588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115300, d150588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115301 q = 1) : d150589 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115301, d150589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115301, d150589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115302 q = 1) : d150590 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115302, d150590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115302, d150590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29092 (p : Pattern) (ha : d94755 p = 1) (hb : d115308 p = 1) : d150596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12290 q = 1) (hb : d94755 q = 1) : d97518 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12290, d97518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12290, d97518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29073 q ha hb
  have h2 (q : Pattern) (ha : d12291 q = 1) (hb : d94755 q = 1) : d97519 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12291, d97519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12291, d97519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12297 q = 1) (hb : d94755 q = 1) : d97525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d97525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29073 q ha hb
    | true =>
      simp only [d12297, d97525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29074 q ha hb
  have h4 (q : Pattern) (ha : d12298 q = 1) (hb : d94755 q = 1) : d97526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d97526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12298, d97526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12299 q = 1) (hb : d94755 q = 1) : d97527 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12299, d97527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12299, d97527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115286 q = 1) : d150569 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115286, d150569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29081 q ha hb
    | true =>
      simp only [d115286, d150569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29086 q ha hb
  have h7 (q : Pattern) (ha : d12374 q = 1) (hb : d94755 q = 1) : d97573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12374, d97573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29075 q ha hb
    | true =>
      simp only [d12374, d97573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12399 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115287 q = 1) : d150570 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115287, d150570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115287, d150570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115288 q = 1) : d150571 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115288, d150571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115288, d150571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d115289 q = 1) : d150572 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115289, d150572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115289, d150572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d115293 q = 1) : d150576 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115293, d150576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115293, d150576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29087 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12418 q ha hb
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115294 q = 1) : d150577 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115294, d150577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115294, d150577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115295 q = 1) : d150578 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115295, d150578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115295, d150578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115296 q = 1) : d150579 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115296, d150579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115296, d150579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d94755 q = 1) (hb : d115297 q = 1) : d150580 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115297, d150580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115297, d150580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94755 q = 1) (hb : d115303 q = 1) : d150591 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115303, d150591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115303, d150591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29091 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12419 q ha hb
  have h19 (q : Pattern) (ha : d94755 q = 1) (hb : d115304 q = 1) : d150592 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115304, d150592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115304, d150592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d94755 q = 1) (hb : d115305 q = 1) : d150593 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115305, d150593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115305, d150593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d94755 q = 1) (hb : d115306 q = 1) : d150594 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115306, d150594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115306, d150594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d94755 q = 1) (hb : d115307 q = 1) : d150595 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115307, d150595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115307, d150595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115308 q = 1) : d150596 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115308, d150596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115308, d150596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29093 (p : Pattern) (ha : d94755 p = 1) (hb : d115314 p = 1) : d150602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12397 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115271 q = 1) : d97508 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115271, d97508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115271, d97508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29072 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115272 q = 1) : d97509 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115272, d97509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115272, d97509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115273 q = 1) : d97510 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115273, d97510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115273, d97510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115274 q = 1) : d97511 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115274, d97511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115274, d97511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115275 q = 1) : d97512 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115275, d97512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115275, d97512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d115309 q = 1) : d150597 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115309, d150597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115309, d150597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29092 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d115310 q = 1) : d150598 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115310, d150598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115310, d150598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115311 q = 1) : d150599 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115311, d150599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115311, d150599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115312 q = 1) : d150600 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115312, d150600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115312, d150600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115313 q = 1) : d150601 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115313, d150601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115313, d150601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115314 q = 1) : d150602 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115314, d150602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115314, d150602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29094 (p : Pattern) (ha : d12438 p = 1) (hb : d94755 p = 1) : d97613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4821 q = 1) (hb : d94753 q = 1) : d4821 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12316 q = 1) (hb : d94755 q = 1) : d97540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d94755, d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12316, d94755, d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4821 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4822 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4822, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12437 q = 1) (hb : d94755 q = 1) : d97612 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12437, d97612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12437, d97612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12438 q = 1) (hb : d94755 q = 1) : d97613 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12438, d97613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12438, d97613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29095 (p : Pattern) (ha : d12442 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d4821 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4822 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d4822, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12441 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12442 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro29096 (p : Pattern) (ha : d12448 p = 1) (hb : d94755 p = 1) : d97619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d94755 q = 1) : d97614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29094 q ha hb
    | true =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d94755 q = 1) : d97615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29095 q ha hb
    | true =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d94755 q = 1) : d97616 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d94755 q = 1) : d97617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12447 q = 1) (hb : d94755 q = 1) : d97618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12447, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12448 q = 1) (hb : d94755 q = 1) : d97619 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12448, d97619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12448, d97619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29097 (p : Pattern) (ha : d12452 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29095 q ha hb
    | true =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12452 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29098 (p : Pattern) (ha : d12458 p = 1) (hb : d94755 p = 1) : d97625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d94755 q = 1) : d97620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29096 q ha hb
    | true =>
      simp only [d12453, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29097 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d94755 q = 1) : d97621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d94755 q = 1) : d97622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d94755 q = 1) : d97623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d94755 q = 1) : d97624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12458 q = 1) (hb : d94755 q = 1) : d97625 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12458, d97625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12458, d97625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29099 (p : Pattern) (ha : d12461 p = 1) (hb : d94755 p = 1) : d97628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d94755 q = 1) : d97614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29094 q ha hb
    | true =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d94755 q = 1) : d97615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29095 q ha hb
    | true =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d94755 q = 1) : d97616 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d94755 q = 1) : d97617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12447 q = 1) (hb : d94755 q = 1) : d97618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12447, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12461 q = 1) (hb : d94755 q = 1) : d97628 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12461, d97628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12461, d97628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29100 (p : Pattern) (ha : d12462 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29095 q ha hb
    | true =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12462 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29101 (p : Pattern) (ha : d12468 p = 1) (hb : d94755 p = 1) : d97634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d94755 q = 1) : d97620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29096 q ha hb
    | true =>
      simp only [d12453, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29097 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d94755 q = 1) : d97621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d94755 q = 1) : d97622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d94755 q = 1) : d97623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d94755 q = 1) : d97624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12463 q = 1) (hb : d94755 q = 1) : d97629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29099 q ha hb
    | true =>
      simp only [d12463, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29100 q ha hb
  have h7 (q : Pattern) (ha : d12464 q = 1) (hb : d94755 q = 1) : d97630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d97630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d97630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12465 q = 1) (hb : d94755 q = 1) : d97631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d97631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12465, d97631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12466 q = 1) (hb : d94755 q = 1) : d97632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d97632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d97632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12467 q = 1) (hb : d94755 q = 1) : d97633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d97633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d97633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12468 q = 1) (hb : d94755 q = 1) : d97634 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12468, d97634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12468, d97634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29102 (p : Pattern) (ha : d12574 p = 1) (hb : d94755 p = 1) : d97684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d94755 q = 1) : d97620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29096 q ha hb
    | true =>
      simp only [d12453, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29097 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d94755 q = 1) : d97621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d94755 q = 1) : d97622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d94755 q = 1) : d97623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d94755 q = 1) : d97624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12569 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29097 q ha hb
    | true =>
      simp only [d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12570 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12571 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12572 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12573 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12574 q = 1) (hb : d94755 q = 1) : d97684 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12574, d97684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12574, d97684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29103 (p : Pattern) (ha : d12580 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12569 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29097 q ha hb
    | true =>
      simp only [d12569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12570 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12571 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12572 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12573 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12575 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29100 q ha hb
    | true =>
      simp only [d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12576 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12577 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12578 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12579 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12580 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29104 (p : Pattern) (ha : d12589 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12575 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29100 q ha hb
    | true =>
      simp only [d12575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12576 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12577 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12578 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12579 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12589 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29105 (p : Pattern) (ha : d12622 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6081 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6082 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6082, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12621 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12622 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro29106 (p : Pattern) (ha : d12668 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12623 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29105 q ha hb
    | true =>
      simp only [d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12624 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12665 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12666 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12667 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12668 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29107 (p : Pattern) (ha : d12674 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12669 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29106 q ha hb
    | true =>
      simp only [d12669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12670 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12671 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12672 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12673 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12674 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29108 (p : Pattern) (ha : d12473 p = 1) (hb : d94755 p = 1) : d97639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d94755 q = 1) : d97614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29094 q ha hb
    | true =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d94755 q = 1) : d97615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29095 q ha hb
    | true =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d94755 q = 1) : d97616 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d94755 q = 1) : d97617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12472 q = 1) (hb : d94755 q = 1) : d97638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d97638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d97638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12473 q = 1) (hb : d94755 q = 1) : d97639 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12473, d97639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12473, d97639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29109 (p : Pattern) (ha : d12475 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29095 q ha hb
    | true =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12475 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29110 (p : Pattern) (ha : d12482 p = 1) (hb : d94755 p = 1) : d97646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d94755 q = 1) : d97614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29094 q ha hb
    | true =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d94755 q = 1) : d97615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29095 q ha hb
    | true =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d94755 q = 1) : d97616 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12480 q = 1) (hb : d94755 q = 1) : d97644 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d97644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d97644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12481 q = 1) (hb : d94755 q = 1) : d97645 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d97645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12481, d97645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12482 q = 1) (hb : d94755 q = 1) : d97646 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12482, d97646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12482, d97646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29111 (p : Pattern) (ha : d12485 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29095 q ha hb
    | true =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29112 (p : Pattern) (ha : d12502 p = 1) (hb : d94755 p = 1) : d150605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12499 q = 1) (hb : d94753 q = 1) : d12499 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12500 q = 1) (hb : d94755 q = 1) : d150603 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12500, d94755, d150603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12500, d94755, d150603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4821 q = 1) (hb : d94753 q = 1) : d4821 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12316 q = 1) (hb : d94755 q = 1) : d97540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d94755, d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d12316, d94755, d97540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12501 q = 1) (hb : d94755 q = 1) : d150604 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12501, d150604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12501, d150604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12502 q = 1) (hb : d94755 q = 1) : d150605 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12502, d150605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12502, d150605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29113 (p : Pattern) (ha : d12508 p = 1) (hb : d94755 p = 1) : d150611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d94755 q = 1) : d150606 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d150606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29112 q ha hb
    | true =>
      simp only [d12503, d150606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d94755 q = 1) : d150607 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d150607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d150607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d94755 q = 1) : d97614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29094 q ha hb
    | true =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d94755 q = 1) : d97615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d94755 q = 1) : d150608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d150608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d150608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d94755 q = 1) : d150609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d150609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d150609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d94755 q = 1) : d150610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d150610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d150610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12508 q = 1) (hb : d94755 q = 1) : d150611 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12508, d150611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12508, d150611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29114 (p : Pattern) (ha : d12537 p = 1) (hb : d94755 p = 1) : d97619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d94755 q = 1) : d97614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29094 q ha hb
    | true =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d94755 q = 1) : d97615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d94755 q = 1) : d97616 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d94755 q = 1) : d97617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d94755 q = 1) : d97618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12537 q = 1) (hb : d94755 q = 1) : d97619 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12537, d97619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12537, d97619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29115 (p : Pattern) (ha : d94755 p = 1) (hb : d115319 p = 1) : d150617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12476 q = 1) (hb : d94755 q = 1) : d97640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d97640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29108 q ha hb
    | true =>
      simp only [d12476, d97640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29109 q ha hb
  have h2 (q : Pattern) (ha : d12477 q = 1) (hb : d94755 q = 1) : d97641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d97641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d97641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12478 q = 1) (hb : d94755 q = 1) : d97642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d97642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12478, d97642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12479 q = 1) (hb : d94755 q = 1) : d97643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d97643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d97643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12486 q = 1) (hb : d94755 q = 1) : d97647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d97647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29110 q ha hb
    | true =>
      simp only [d12486, d97647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29111 q ha hb
  have h6 (q : Pattern) (ha : d12487 q = 1) (hb : d94755 q = 1) : d97648 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d97648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d97648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12488 q = 1) (hb : d94755 q = 1) : d97649 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d97649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12488, d97649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12509 q = 1) (hb : d94755 q = 1) : d150612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d150612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29113 q ha hb
    | true =>
      simp only [d12509, d150612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29096 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115315 q = 1) : d150613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d150613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115315, d150613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d12538 q = 1) (hb : d94755 q = 1) : d97620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29114 q ha hb
    | true =>
      simp only [d12538, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12539 q = 1) (hb : d94755 q = 1) : d97661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d97661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12539, d97661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115316 q = 1) : d150614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d150614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115316, d150614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115317 q = 1) : d150615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d150615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115317, d150615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115318 q = 1) : d150616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d150616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115318, d150616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115319 q = 1) : d150617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115319, d150617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115319, d150617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29116 (p : Pattern) (ha : d12544 p = 1) (hb : d94755 p = 1) : d97666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d94755 q = 1) : d97614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29094 q ha hb
    | true =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d94755 q = 1) : d97615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29095 q ha hb
    | true =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d94755 q = 1) : d97616 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d94755 q = 1) : d97617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12472 q = 1) (hb : d94755 q = 1) : d97638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d97638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d97638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12544 q = 1) (hb : d94755 q = 1) : d97666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12544, d97666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12544, d97666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29117 (p : Pattern) (ha : d12545 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29095 q ha hb
    | true =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12545 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29118 (p : Pattern) (ha : d12550 p = 1) (hb : d94755 p = 1) : d97671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d94755 q = 1) : d97614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29094 q ha hb
    | true =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d94755 q = 1) : d97615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29095 q ha hb
    | true =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d94755 q = 1) : d97616 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12480 q = 1) (hb : d94755 q = 1) : d97644 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d97644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d97644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12481 q = 1) (hb : d94755 q = 1) : d97645 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d97645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12481, d97645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12550 q = 1) (hb : d94755 q = 1) : d97671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12550, d97671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12550, d97671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29119 (p : Pattern) (ha : d12551 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29095 q ha hb
    | true =>
      simp only [d12443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12551 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29120 (p : Pattern) (ha : d12555 p = 1) (hb : d94755 p = 1) : d150618 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d94755 q = 1) : d150606 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d150606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29112 q ha hb
    | true =>
      simp only [d12503, d150606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d94755 q = 1) : d150607 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d150607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d150607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d94755 q = 1) : d97614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29094 q ha hb
    | true =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d94755 q = 1) : d97615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d94755 q = 1) : d150608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d150608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d150608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d94755 q = 1) : d150609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d150609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d150609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d94755 q = 1) : d150610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d150610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d150610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12555 q = 1) (hb : d94755 q = 1) : d150618 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12555, d150618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12555, d150618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29121 (p : Pattern) (ha : d12561 p = 1) (hb : d94755 p = 1) : d97628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d94755 q = 1) : d97614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29094 q ha hb
    | true =>
      simp only [d12439, d97614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d94755 q = 1) : d97615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d97615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d94755 q = 1) : d97616 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d97616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d94755 q = 1) : d97617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d97617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d94755 q = 1) : d97618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d97618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12561 q = 1) (hb : d94755 q = 1) : d97628 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12561, d97628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12561, d97628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29122 (p : Pattern) (ha : d94755 p = 1) (hb : d115324 p = 1) : d150624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12476 q = 1) (hb : d94755 q = 1) : d97640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d97640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29108 q ha hb
    | true =>
      simp only [d12476, d97640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29109 q ha hb
  have h2 (q : Pattern) (ha : d12477 q = 1) (hb : d94755 q = 1) : d97641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d97641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d97641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12478 q = 1) (hb : d94755 q = 1) : d97642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d97642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12478, d97642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12479 q = 1) (hb : d94755 q = 1) : d97643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d97643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d97643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12486 q = 1) (hb : d94755 q = 1) : d97647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d97647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29110 q ha hb
    | true =>
      simp only [d12486, d97647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29111 q ha hb
  have h6 (q : Pattern) (ha : d12487 q = 1) (hb : d94755 q = 1) : d97648 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d97648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d97648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12488 q = 1) (hb : d94755 q = 1) : d97649 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d97649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12488, d97649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12509 q = 1) (hb : d94755 q = 1) : d150612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d150612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29113 q ha hb
    | true =>
      simp only [d12509, d150612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29096 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115315 q = 1) : d150613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d150613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115315, d150613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d12538 q = 1) (hb : d94755 q = 1) : d97620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29114 q ha hb
    | true =>
      simp only [d12538, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12539 q = 1) (hb : d94755 q = 1) : d97661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d97661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12539, d97661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115316 q = 1) : d150614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d150614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115316, d150614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115317 q = 1) : d150615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d150615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115317, d150615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115318 q = 1) : d150616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d150616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115318, d150616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12546 q = 1) (hb : d94755 q = 1) : d97667 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12546, d97667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29116 q ha hb
    | true =>
      simp only [d12546, d97667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29117 q ha hb
  have h16 (q : Pattern) (ha : d12547 q = 1) (hb : d94755 q = 1) : d97668 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12547, d97668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12547, d97668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12548 q = 1) (hb : d94755 q = 1) : d97669 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12548, d97669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12548, d97669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12549 q = 1) (hb : d94755 q = 1) : d97670 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12549, d97670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12549, d97670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12552 q = 1) (hb : d94755 q = 1) : d97672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12552, d97672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29118 q ha hb
    | true =>
      simp only [d12552, d97672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29119 q ha hb
  have h20 (q : Pattern) (ha : d12553 q = 1) (hb : d94755 q = 1) : d97673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12553, d97673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12553, d97673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12554 q = 1) (hb : d94755 q = 1) : d97674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12554, d97674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12554, d97674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12556 q = 1) (hb : d94755 q = 1) : d150619 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d150619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29120 q ha hb
    | true =>
      simp only [d12556, d150619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29099 q ha hb
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115320 q = 1) : d150620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d150620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d115320, d150620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d12562 q = 1) (hb : d94755 q = 1) : d97629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29121 q ha hb
    | true =>
      simp only [d12562, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12563 q = 1) (hb : d94755 q = 1) : d97678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d97678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12563, d97678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94755 q = 1) (hb : d115321 q = 1) : d150621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d150621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115321, d150621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d94755 q = 1) (hb : d115322 q = 1) : d150622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115322, d150622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115322, d150622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94755 q = 1) (hb : d115323 q = 1) : d150623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115323, d150623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d115323, d150623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94755 q = 1) (hb : d115324 q = 1) : d150624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115324, d150624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115324, d150624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro29123 (p : Pattern) (ha : d94755 p = 1) (hb : d115331 p = 1) : d150631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12556 q = 1) (hb : d94755 q = 1) : d150619 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d150619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29120 q ha hb
    | true =>
      simp only [d12556, d150619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29099 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115320 q = 1) : d150620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d150620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115320, d150620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12562 q = 1) (hb : d94755 q = 1) : d97629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29121 q ha hb
    | true =>
      simp only [d12562, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12563 q = 1) (hb : d94755 q = 1) : d97678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d97678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12563, d97678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115321 q = 1) : d150621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d150621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115321, d150621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115329 q = 1) : d150629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115329, d150629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115329, d150629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115330 q = 1) : d150630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115330, d150630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115330, d150630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115331 q = 1) : d150631 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115331, d150631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115331, d150631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29124 (p : Pattern) (ha : d12610 p = 1) (hb : d94755 p = 1) : d150639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12598 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12607 q = 1) (hb : d94753 q = 1) : d12607 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12608 q = 1) (hb : d94755 q = 1) : d150637 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12608, d94755, d150637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12608, d94755, d150637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12389 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6081 q = 1) (hb : d94753 q = 1) : d6081 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12390 q = 1) (hb : d94755 q = 1) : d97585 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d94755, d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d12390, d94755, d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12609 q = 1) (hb : d94755 q = 1) : d150638 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12609, d150638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12609, d150638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12610 q = 1) (hb : d94755 q = 1) : d150639 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12610, d150639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12610, d150639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29125 (p : Pattern) (ha : d12614 p = 1) (hb : d94755 p = 1) : d97707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6081 q = 1) (hb : d94753 q = 1) : d6081 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12390 q = 1) (hb : d94755 q = 1) : d97585 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d94755, d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12390, d94755, d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6081 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6082 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d6082, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12613 q = 1) (hb : d94755 q = 1) : d97706 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12613, d97706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12613, d97706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12614 q = 1) (hb : d94755 q = 1) : d97707 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12614, d97707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12614, d97707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29126 (p : Pattern) (ha : d12620 p = 1) (hb : d94755 p = 1) : d150645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12611 q = 1) (hb : d94755 q = 1) : d150640 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12611, d150640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29124 q ha hb
    | true =>
      simp only [d12611, d150640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12612 q = 1) (hb : d94755 q = 1) : d150641 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12612, d150641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12612, d150641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12615 q = 1) (hb : d94755 q = 1) : d97708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29125 q ha hb
    | true =>
      simp only [d12615, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12616 q = 1) (hb : d94755 q = 1) : d97709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12617 q = 1) (hb : d94755 q = 1) : d150642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12617, d150642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12617, d150642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12618 q = 1) (hb : d94755 q = 1) : d150643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12618, d150643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12618, d150643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12619 q = 1) (hb : d94755 q = 1) : d150644 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12619, d150644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12619, d150644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12620 q = 1) (hb : d94755 q = 1) : d150645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12620, d150645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12620, d150645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29127 (p : Pattern) (ha : d12628 p = 1) (hb : d94755 p = 1) : d97713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d94755 q = 1) : d97708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29125 q ha hb
    | true =>
      simp only [d12615, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d94755 q = 1) : d97709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12623 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29105 q ha hb
    | true =>
      simp only [d12623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12624 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12625 q = 1) (hb : d94755 q = 1) : d97710 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12625, d97710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12625, d97710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12626 q = 1) (hb : d94755 q = 1) : d97711 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12626, d97711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12626, d97711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12627 q = 1) (hb : d94755 q = 1) : d97712 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12627, d97712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12627, d97712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12628 q = 1) (hb : d94755 q = 1) : d97713 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12628, d97713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12628, d97713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29128 (p : Pattern) (ha : d12657 p = 1) (hb : d94755 p = 1) : d97713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d94755 q = 1) : d97708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29125 q ha hb
    | true =>
      simp only [d12615, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d94755 q = 1) : d97709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12654 q = 1) (hb : d94755 q = 1) : d97710 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12654, d97710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12654, d97710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12655 q = 1) (hb : d94755 q = 1) : d97711 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12655, d97711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12655, d97711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12656 q = 1) (hb : d94755 q = 1) : d97712 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12656, d97712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12656, d97712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12657 q = 1) (hb : d94755 q = 1) : d97713 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12657, d97713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12657, d97713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29129 (p : Pattern) (ha : d94755 p = 1) (hb : d115341 p = 1) : d150651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12629 q = 1) (hb : d94755 q = 1) : d150646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12629, d150646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29126 q ha hb
    | true =>
      simp only [d12629, d150646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29127 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115337 q = 1) : d150647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115337, d150647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115337, d150647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12658 q = 1) (hb : d94755 q = 1) : d97716 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12658, d97716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29128 q ha hb
    | true =>
      simp only [d12658, d97716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12659 q = 1) (hb : d94755 q = 1) : d97717 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12659, d97717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12659, d97717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115338 q = 1) : d150648 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115338, d150648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115338, d150648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115339 q = 1) : d150649 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115339, d150649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115339, d150649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115340 q = 1) : d150650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115340, d150650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115340, d150650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115341 q = 1) : d150651 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115341, d150651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115341, d150651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29130 (p : Pattern) (ha : d94755 p = 1) (hb : d115347 p = 1) : d150657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12459 q = 1) (hb : d94755 q = 1) : d97626 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12459, d97626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12459, d97626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29098 q ha hb
  have h2 (q : Pattern) (ha : d12460 q = 1) (hb : d94755 q = 1) : d97627 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12460, d97627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12460, d97627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12469 q = 1) (hb : d94755 q = 1) : d97635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d97635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29098 q ha hb
    | true =>
      simp only [d12469, d97635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29101 q ha hb
  have h4 (q : Pattern) (ha : d12470 q = 1) (hb : d94755 q = 1) : d97636 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d97636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12470, d97636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12471 q = 1) (hb : d94755 q = 1) : d97637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12471, d97637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12471, d97637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115325 q = 1) : d150625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115325, d150625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29115 q ha hb
    | true =>
      simp only [d115325, d150625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29122 q ha hb
  have h7 (q : Pattern) (ha : d12581 q = 1) (hb : d94755 q = 1) : d97685 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12581, d97685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29102 q ha hb
    | true =>
      simp only [d12581, d97685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29103 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115326 q = 1) : d150626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115326, d150626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115326, d150626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115327 q = 1) : d150627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115327, d150627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115327, d150627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d115328 q = 1) : d150628 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115328, d150628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115328, d150628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d115332 q = 1) : d150632 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115332, d150632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115332, d150632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29123 q ha hb
  have h12 (q : Pattern) (ha : d12590 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29104 q ha hb
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115333 q = 1) : d150633 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115333, d150633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115333, d150633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115334 q = 1) : d150634 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115334, d150634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115334, d150634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115335 q = 1) : d150635 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115335, d150635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115335, d150635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d94755 q = 1) (hb : d115336 q = 1) : d150636 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115336, d150636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115336, d150636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94755 q = 1) (hb : d115342 q = 1) : d150652 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115342, d150652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115342, d150652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29129 q ha hb
  have h18 (q : Pattern) (ha : d12675 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29107 q ha hb
  have h19 (q : Pattern) (ha : d94755 q = 1) (hb : d115343 q = 1) : d150653 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115343, d150653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115343, d150653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d94755 q = 1) (hb : d115344 q = 1) : d150654 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115344, d150654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115344, d150654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d94755 q = 1) (hb : d115345 q = 1) : d150655 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115345, d150655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115345, d150655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d94755 q = 1) (hb : d115346 q = 1) : d150656 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115346, d150656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115346, d150656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115347 q = 1) : d150657 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115347, d150657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115347, d150657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29131 (p : Pattern) (ha : d94755 p = 1) (hb : d115353 p = 1) : d150663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d115348 q = 1) : d150658 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115348, d150658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115348, d150658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29130 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115349 q = 1) : d150659 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115349, d150659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115349, d150659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d115350 q = 1) : d150660 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115350, d150660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115350, d150660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d115351 q = 1) : d150661 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115351, d150661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115351, d150661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115352 q = 1) : d150662 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115352, d150662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115352, d150662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115353 q = 1) : d150663 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115353, d150663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115353, d150663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29132 (p : Pattern) (ha : d12693 p = 1) (hb : d94755 p = 1) : d97737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12690 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4916 q = 1) (hb : d94753 q = 1) : d4916 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12691 q = 1) (hb : d94755 q = 1) : d97735 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d94755, d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12691, d94755, d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4916 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4917 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4917, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12692 q = 1) (hb : d94755 q = 1) : d97736 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12692, d97736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12692, d97736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12693 q = 1) (hb : d94755 q = 1) : d97737 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12693, d97737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12693, d97737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29133 (p : Pattern) (ha : d12697 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d4916 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4917 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d4917, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12696 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12697 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro29134 (p : Pattern) (ha : d12703 p = 1) (hb : d94755 p = 1) : d97743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29132 q ha hb
    | true =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29133 q ha hb
    | true =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d94755 q = 1) : d97741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12702 q = 1) (hb : d94755 q = 1) : d97742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12702, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12703 q = 1) (hb : d94755 q = 1) : d97743 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12703, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12703, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29135 (p : Pattern) (ha : d12707 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29133 q ha hb
    | true =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12707 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29136 (p : Pattern) (ha : d12713 p = 1) (hb : d94755 p = 1) : d97749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d94755 q = 1) : d97744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29134 q ha hb
    | true =>
      simp only [d12708, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29135 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d94755 q = 1) : d97745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d94755 q = 1) : d97746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d94755 q = 1) : d97747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d94755 q = 1) : d97748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12713 q = 1) (hb : d94755 q = 1) : d97749 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12713, d97749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12713, d97749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29137 (p : Pattern) (ha : d12716 p = 1) (hb : d94755 p = 1) : d97752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29132 q ha hb
    | true =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29133 q ha hb
    | true =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d94755 q = 1) : d97741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12702 q = 1) (hb : d94755 q = 1) : d97742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12702, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12716 q = 1) (hb : d94755 q = 1) : d97752 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12716, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12716, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29138 (p : Pattern) (ha : d12717 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29133 q ha hb
    | true =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12717 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29139 (p : Pattern) (ha : d12723 p = 1) (hb : d94755 p = 1) : d97758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d94755 q = 1) : d97744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29134 q ha hb
    | true =>
      simp only [d12708, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29135 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d94755 q = 1) : d97745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d94755 q = 1) : d97746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d94755 q = 1) : d97747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d94755 q = 1) : d97748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12718 q = 1) (hb : d94755 q = 1) : d97753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29137 q ha hb
    | true =>
      simp only [d12718, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29138 q ha hb
  have h7 (q : Pattern) (ha : d12719 q = 1) (hb : d94755 q = 1) : d97754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d97754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d97754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12720 q = 1) (hb : d94755 q = 1) : d97755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d97755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12720, d97755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12721 q = 1) (hb : d94755 q = 1) : d97756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d97756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d97756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12722 q = 1) (hb : d94755 q = 1) : d97757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d97757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d97757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12723 q = 1) (hb : d94755 q = 1) : d97758 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12723, d97758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12723, d97758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29140 (p : Pattern) (ha : d12833 p = 1) (hb : d94755 p = 1) : d97808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d94755 q = 1) : d97744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29134 q ha hb
    | true =>
      simp only [d12708, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29135 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d94755 q = 1) : d97745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d94755 q = 1) : d97746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d94755 q = 1) : d97747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d94755 q = 1) : d97748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12828 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29135 q ha hb
    | true =>
      simp only [d12828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12829 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12830 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12831 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12832 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12833 q = 1) (hb : d94755 q = 1) : d97808 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12833, d97808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12833, d97808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29141 (p : Pattern) (ha : d12839 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12828 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29135 q ha hb
    | true =>
      simp only [d12828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12829 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12830 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12831 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12832 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12834 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29138 q ha hb
    | true =>
      simp only [d12834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12835 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12836 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12837 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12838 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12839 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29142 (p : Pattern) (ha : d12848 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12834 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29138 q ha hb
    | true =>
      simp only [d12834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12835 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12836 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12837 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12838 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12848 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29143 (p : Pattern) (ha : d12885 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6214 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6214, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12884 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12885 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro29144 (p : Pattern) (ha : d12935 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12886 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29143 q ha hb
    | true =>
      simp only [d12886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12887 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12932 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12933 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12934 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12935 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29145 (p : Pattern) (ha : d12941 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12936 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29144 q ha hb
    | true =>
      simp only [d12936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12937 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12938 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12939 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12940 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12941 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29146 (p : Pattern) (ha : d12728 p = 1) (hb : d94755 p = 1) : d97763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29132 q ha hb
    | true =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29133 q ha hb
    | true =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d94755 q = 1) : d97741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12727 q = 1) (hb : d94755 q = 1) : d97762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d97762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d97762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12728 q = 1) (hb : d94755 q = 1) : d97763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12728, d97763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12728, d97763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29147 (p : Pattern) (ha : d12730 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29133 q ha hb
    | true =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12730 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29148 (p : Pattern) (ha : d12737 p = 1) (hb : d94755 p = 1) : d97770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29132 q ha hb
    | true =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29133 q ha hb
    | true =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12735 q = 1) (hb : d94755 q = 1) : d97768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d97768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d97768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12736 q = 1) (hb : d94755 q = 1) : d97769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d97769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12736, d97769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12737 q = 1) (hb : d94755 q = 1) : d97770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12737, d97770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12737, d97770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29149 (p : Pattern) (ha : d12740 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29133 q ha hb
    | true =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29150 (p : Pattern) (ha : d12757 p = 1) (hb : d94755 p = 1) : d150667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12754 q = 1) (hb : d94753 q = 1) : d12754 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12755 q = 1) (hb : d94755 q = 1) : d150665 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12755, d94755, d150665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12755, d94755, d150665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12690 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4916 q = 1) (hb : d94753 q = 1) : d4916 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12691 q = 1) (hb : d94755 q = 1) : d97735 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d94755, d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d12691, d94755, d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12756 q = 1) (hb : d94755 q = 1) : d150666 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12756, d150666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12756, d150666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12757 q = 1) (hb : d94755 q = 1) : d150667 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12757, d150667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12757, d150667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29151 (p : Pattern) (ha : d12763 p = 1) (hb : d94755 p = 1) : d150673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d94755 q = 1) : d150668 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d150668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29150 q ha hb
    | true =>
      simp only [d12758, d150668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d94755 q = 1) : d150669 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d150669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d150669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29132 q ha hb
    | true =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d94755 q = 1) : d150670 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d150670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d150670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d94755 q = 1) : d150671 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d150671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d150671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d94755 q = 1) : d150672 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d150672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d150672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12763 q = 1) (hb : d94755 q = 1) : d150673 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12763, d150673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12763, d150673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29152 (p : Pattern) (ha : d12796 p = 1) (hb : d94755 p = 1) : d97743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29132 q ha hb
    | true =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d94755 q = 1) : d97741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d94755 q = 1) : d97742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12796 q = 1) (hb : d94755 q = 1) : d97743 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12796, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12796, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29153 (p : Pattern) (ha : d94755 p = 1) (hb : d115359 p = 1) : d150679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12731 q = 1) (hb : d94755 q = 1) : d97764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d97764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29146 q ha hb
    | true =>
      simp only [d12731, d97764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29147 q ha hb
  have h2 (q : Pattern) (ha : d12732 q = 1) (hb : d94755 q = 1) : d97765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d97765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d97765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12733 q = 1) (hb : d94755 q = 1) : d97766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d97766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12733, d97766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12734 q = 1) (hb : d94755 q = 1) : d97767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d97767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d97767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12741 q = 1) (hb : d94755 q = 1) : d97771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d97771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29148 q ha hb
    | true =>
      simp only [d12741, d97771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29149 q ha hb
  have h6 (q : Pattern) (ha : d12742 q = 1) (hb : d94755 q = 1) : d97772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d97772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d97772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12743 q = 1) (hb : d94755 q = 1) : d97773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d97773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12743, d97773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12764 q = 1) (hb : d94755 q = 1) : d150674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d150674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29151 q ha hb
    | true =>
      simp only [d12764, d150674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29134 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115355 q = 1) : d150675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d150675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115355, d150675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d12797 q = 1) (hb : d94755 q = 1) : d97744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29152 q ha hb
    | true =>
      simp only [d12797, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12798 q = 1) (hb : d94755 q = 1) : d97785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d97785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12798, d97785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115356 q = 1) : d150676 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d150676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115356, d150676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115357 q = 1) : d150677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d150677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115357, d150677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115358 q = 1) : d150678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d150678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115358, d150678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115359 q = 1) : d150679 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115359, d150679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115359, d150679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29154 (p : Pattern) (ha : d12803 p = 1) (hb : d94755 p = 1) : d97790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29132 q ha hb
    | true =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29133 q ha hb
    | true =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d94755 q = 1) : d97741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12727 q = 1) (hb : d94755 q = 1) : d97762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d97762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d97762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12803 q = 1) (hb : d94755 q = 1) : d97790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12803, d97790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12803, d97790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29155 (p : Pattern) (ha : d12804 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29133 q ha hb
    | true =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12804 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29156 (p : Pattern) (ha : d12809 p = 1) (hb : d94755 p = 1) : d97795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29132 q ha hb
    | true =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29133 q ha hb
    | true =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12735 q = 1) (hb : d94755 q = 1) : d97768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d97768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d97768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12736 q = 1) (hb : d94755 q = 1) : d97769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d97769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12736, d97769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12809 q = 1) (hb : d94755 q = 1) : d97795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12809, d97795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12809, d97795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29157 (p : Pattern) (ha : d12810 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29133 q ha hb
    | true =>
      simp only [d12698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12810 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29158 (p : Pattern) (ha : d12814 p = 1) (hb : d94755 p = 1) : d150680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d94755 q = 1) : d150668 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d150668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29150 q ha hb
    | true =>
      simp only [d12758, d150668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d94755 q = 1) : d150669 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d150669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d150669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29132 q ha hb
    | true =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d94755 q = 1) : d150670 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d150670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d150670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d94755 q = 1) : d150671 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d150671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d150671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d94755 q = 1) : d150672 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d150672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d150672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12814 q = 1) (hb : d94755 q = 1) : d150680 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12814, d150680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12814, d150680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29159 (p : Pattern) (ha : d12820 p = 1) (hb : d94755 p = 1) : d97752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d94755 q = 1) : d97738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29132 q ha hb
    | true =>
      simp only [d12694, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d94755 q = 1) : d97739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d94755 q = 1) : d97740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d94755 q = 1) : d97741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d94755 q = 1) : d97742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12820 q = 1) (hb : d94755 q = 1) : d97752 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12820, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12820, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29160 (p : Pattern) (ha : d94755 p = 1) (hb : d115364 p = 1) : d150686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12731 q = 1) (hb : d94755 q = 1) : d97764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d97764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29146 q ha hb
    | true =>
      simp only [d12731, d97764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29147 q ha hb
  have h2 (q : Pattern) (ha : d12732 q = 1) (hb : d94755 q = 1) : d97765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d97765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d97765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12733 q = 1) (hb : d94755 q = 1) : d97766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d97766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12733, d97766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12734 q = 1) (hb : d94755 q = 1) : d97767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d97767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d97767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12741 q = 1) (hb : d94755 q = 1) : d97771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d97771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29148 q ha hb
    | true =>
      simp only [d12741, d97771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29149 q ha hb
  have h6 (q : Pattern) (ha : d12742 q = 1) (hb : d94755 q = 1) : d97772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d97772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d97772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12743 q = 1) (hb : d94755 q = 1) : d97773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d97773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12743, d97773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12764 q = 1) (hb : d94755 q = 1) : d150674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d150674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29151 q ha hb
    | true =>
      simp only [d12764, d150674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29134 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115355 q = 1) : d150675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d150675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115355, d150675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d12797 q = 1) (hb : d94755 q = 1) : d97744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29152 q ha hb
    | true =>
      simp only [d12797, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12798 q = 1) (hb : d94755 q = 1) : d97785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d97785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12798, d97785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115356 q = 1) : d150676 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d150676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115356, d150676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115357 q = 1) : d150677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d150677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115357, d150677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115358 q = 1) : d150678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d150678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115358, d150678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12805 q = 1) (hb : d94755 q = 1) : d97791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12805, d97791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29154 q ha hb
    | true =>
      simp only [d12805, d97791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29155 q ha hb
  have h16 (q : Pattern) (ha : d12806 q = 1) (hb : d94755 q = 1) : d97792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12806, d97792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12806, d97792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12807 q = 1) (hb : d94755 q = 1) : d97793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12807, d97793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12807, d97793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12808 q = 1) (hb : d94755 q = 1) : d97794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12808, d97794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12808, d97794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12811 q = 1) (hb : d94755 q = 1) : d97796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12811, d97796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29156 q ha hb
    | true =>
      simp only [d12811, d97796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29157 q ha hb
  have h20 (q : Pattern) (ha : d12812 q = 1) (hb : d94755 q = 1) : d97797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12812, d97797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12812, d97797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12813 q = 1) (hb : d94755 q = 1) : d97798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12813, d97798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12813, d97798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12815 q = 1) (hb : d94755 q = 1) : d150681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d150681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29158 q ha hb
    | true =>
      simp only [d12815, d150681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29137 q ha hb
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115360 q = 1) : d150682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d150682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d115360, d150682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d12821 q = 1) (hb : d94755 q = 1) : d97753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29159 q ha hb
    | true =>
      simp only [d12821, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12822 q = 1) (hb : d94755 q = 1) : d97802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d97802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12822, d97802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94755 q = 1) (hb : d115361 q = 1) : d150683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d150683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115361, d150683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d94755 q = 1) (hb : d115362 q = 1) : d150684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115362, d150684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115362, d150684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94755 q = 1) (hb : d115363 q = 1) : d150685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115363, d150685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d115363, d150685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94755 q = 1) (hb : d115364 q = 1) : d150686 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115364, d150686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115364, d150686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro29161 (p : Pattern) (ha : d94755 p = 1) (hb : d115371 p = 1) : d150693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12815 q = 1) (hb : d94755 q = 1) : d150681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d150681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29158 q ha hb
    | true =>
      simp only [d12815, d150681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29137 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115360 q = 1) : d150682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d150682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115360, d150682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12821 q = 1) (hb : d94755 q = 1) : d97753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29159 q ha hb
    | true =>
      simp only [d12821, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12822 q = 1) (hb : d94755 q = 1) : d97802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d97802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12822, d97802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115361 q = 1) : d150683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d150683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115361, d150683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115369 q = 1) : d150691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115369, d150691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115369, d150691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115370 q = 1) : d150692 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115370, d150692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115370, d150692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115371 q = 1) : d150693 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115371, d150693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115371, d150693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29162 (p : Pattern) (ha : d12873 p = 1) (hb : d94755 p = 1) : d150701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12866 q = 1) (hb : d94753 q = 1) : d12866 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12867 q = 1) (hb : d94755 q = 1) : d150699 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12867, d94755, d150699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12867, d94755, d150699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12870 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6213 q = 1) (hb : d94753 q = 1) : d6213 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12871 q = 1) (hb : d94755 q = 1) : d97822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d94755, d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d12871, d94755, d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12872 q = 1) (hb : d94755 q = 1) : d150700 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12872, d150700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12872, d150700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12873 q = 1) (hb : d94755 q = 1) : d150701 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12873, d150701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12873, d150701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29163 (p : Pattern) (ha : d12877 p = 1) (hb : d94755 p = 1) : d97832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12870 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6213 q = 1) (hb : d94753 q = 1) : d6213 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12871 q = 1) (hb : d94755 q = 1) : d97822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d94755, d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12871, d94755, d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6213 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6214 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d6214, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12876 q = 1) (hb : d94755 q = 1) : d97831 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12876, d97831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12876, d97831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12877 q = 1) (hb : d94755 q = 1) : d97832 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12877, d97832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12877, d97832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29164 (p : Pattern) (ha : d12883 p = 1) (hb : d94755 p = 1) : d150707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12874 q = 1) (hb : d94755 q = 1) : d150702 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12874, d150702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29162 q ha hb
    | true =>
      simp only [d12874, d150702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12875 q = 1) (hb : d94755 q = 1) : d150703 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12875, d150703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12875, d150703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12878 q = 1) (hb : d94755 q = 1) : d97833 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29163 q ha hb
    | true =>
      simp only [d12878, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12879 q = 1) (hb : d94755 q = 1) : d97834 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12880 q = 1) (hb : d94755 q = 1) : d150704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12880, d150704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12880, d150704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12881 q = 1) (hb : d94755 q = 1) : d150705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12881, d150705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12881, d150705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12882 q = 1) (hb : d94755 q = 1) : d150706 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12882, d150706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12882, d150706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12883 q = 1) (hb : d94755 q = 1) : d150707 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12883, d150707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12883, d150707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29165 (p : Pattern) (ha : d12891 p = 1) (hb : d94755 p = 1) : d97838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d94755 q = 1) : d97833 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29163 q ha hb
    | true =>
      simp only [d12878, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d94755 q = 1) : d97834 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12886 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29143 q ha hb
    | true =>
      simp only [d12886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12887 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12888 q = 1) (hb : d94755 q = 1) : d97835 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12888, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12888, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12889 q = 1) (hb : d94755 q = 1) : d97836 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12889, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12889, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12890 q = 1) (hb : d94755 q = 1) : d97837 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12890, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12890, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12891 q = 1) (hb : d94755 q = 1) : d97838 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12891, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12891, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29166 (p : Pattern) (ha : d12924 p = 1) (hb : d94755 p = 1) : d97838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d94755 q = 1) : d97833 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29163 q ha hb
    | true =>
      simp only [d12878, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d94755 q = 1) : d97834 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12921 q = 1) (hb : d94755 q = 1) : d97835 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12921, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12921, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12922 q = 1) (hb : d94755 q = 1) : d97836 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12922, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12922, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12923 q = 1) (hb : d94755 q = 1) : d97837 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12923, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12923, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12924 q = 1) (hb : d94755 q = 1) : d97838 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12924, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12924, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29167 (p : Pattern) (ha : d94755 p = 1) (hb : d115381 p = 1) : d150713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12892 q = 1) (hb : d94755 q = 1) : d150708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12892, d150708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29164 q ha hb
    | true =>
      simp only [d12892, d150708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29165 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115377 q = 1) : d150709 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115377, d150709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115377, d150709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12925 q = 1) (hb : d94755 q = 1) : d97841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12925, d97841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29166 q ha hb
    | true =>
      simp only [d12925, d97841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12926 q = 1) (hb : d94755 q = 1) : d97842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12926, d97842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12926, d97842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115378 q = 1) : d150710 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115378, d150710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115378, d150710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115379 q = 1) : d150711 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115379, d150711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115379, d150711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115380 q = 1) : d150712 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115380, d150712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115380, d150712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115381 q = 1) : d150713 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115381, d150713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115381, d150713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29168 (p : Pattern) (ha : d94755 p = 1) (hb : d115387 p = 1) : d150719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12714 q = 1) (hb : d94755 q = 1) : d97750 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12714, d97750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12714, d97750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29136 q ha hb
  have h2 (q : Pattern) (ha : d12715 q = 1) (hb : d94755 q = 1) : d97751 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12715, d97751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12715, d97751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12724 q = 1) (hb : d94755 q = 1) : d97759 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d97759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29136 q ha hb
    | true =>
      simp only [d12724, d97759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29139 q ha hb
  have h4 (q : Pattern) (ha : d12725 q = 1) (hb : d94755 q = 1) : d97760 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d97760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12725, d97760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12726 q = 1) (hb : d94755 q = 1) : d97761 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12726, d97761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12726, d97761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115365 q = 1) : d150687 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115365, d150687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29153 q ha hb
    | true =>
      simp only [d115365, d150687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29160 q ha hb
  have h7 (q : Pattern) (ha : d12840 q = 1) (hb : d94755 q = 1) : d97809 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12840, d97809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29140 q ha hb
    | true =>
      simp only [d12840, d97809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29141 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115366 q = 1) : d150688 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115366, d150688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115366, d150688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115367 q = 1) : d150689 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115367, d150689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115367, d150689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d115368 q = 1) : d150690 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115368, d150690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115368, d150690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d115372 q = 1) : d150694 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115372, d150694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115372, d150694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29161 q ha hb
  have h12 (q : Pattern) (ha : d12849 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29142 q ha hb
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115373 q = 1) : d150695 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115373, d150695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115373, d150695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115374 q = 1) : d150696 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115374, d150696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115374, d150696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115375 q = 1) : d150697 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115375, d150697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115375, d150697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d94755 q = 1) (hb : d115376 q = 1) : d150698 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115376, d150698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115376, d150698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94755 q = 1) (hb : d115382 q = 1) : d150714 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115382, d150714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115382, d150714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29167 q ha hb
  have h18 (q : Pattern) (ha : d12942 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29145 q ha hb
  have h19 (q : Pattern) (ha : d94755 q = 1) (hb : d115383 q = 1) : d150715 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115383, d150715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115383, d150715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d94755 q = 1) (hb : d115384 q = 1) : d150716 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115384, d150716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115384, d150716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d94755 q = 1) (hb : d115385 q = 1) : d150717 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115385, d150717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115385, d150717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d94755 q = 1) (hb : d115386 q = 1) : d150718 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115386, d150718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115386, d150718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115387 q = 1) : d150719 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115387, d150719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115387, d150719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29169 (p : Pattern) (ha : d94755 p = 1) (hb : d115393 p = 1) : d150725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d115388 q = 1) : d150720 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115388, d150720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115388, d150720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29168 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115389 q = 1) : d150721 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115389, d150721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115389, d150721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d115390 q = 1) : d150722 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115390, d150722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115390, d150722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d115391 q = 1) : d150723 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115391, d150723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115391, d150723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115392 q = 1) : d150724 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115392, d150724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115392, d150724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115393 q = 1) : d150725 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115393, d150725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115393, d150725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29170 (p : Pattern) (ha : d12967 p = 1) (hb : d94755 p = 1) : d150730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12959 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5026 q = 1) (hb : d94753 q = 1) : d5026 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12960 q = 1) (hb : d94755 q = 1) : d150728 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d94755, d150728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12960, d94755, d150728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12964 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12965 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d12965, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12966 q = 1) (hb : d94755 q = 1) : d150729 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12966, d150729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12966, d150729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12967 q = 1) (hb : d94755 q = 1) : d150730 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12967, d150730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12967, d150730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29171 (p : Pattern) (ha : d12971 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12964 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12965 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12965, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12970 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12971 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro29172 (p : Pattern) (ha : d12977 p = 1) (hb : d94755 p = 1) : d150736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d94755 q = 1) : d150731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29170 q ha hb
    | true =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d94755 q = 1) : d150732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d94755 q = 1) : d150733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d94755 q = 1) : d150734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d94755 q = 1) : d150735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d150735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d150735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12977 q = 1) (hb : d94755 q = 1) : d150736 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12977, d150736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12977, d150736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29173 (p : Pattern) (ha : d12981 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12981 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29174 (p : Pattern) (ha : d12987 p = 1) (hb : d94755 p = 1) : d150742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d94755 q = 1) : d150737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d150737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29172 q ha hb
    | true =>
      simp only [d12982, d150737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29173 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d94755 q = 1) : d150738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d150738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d150738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d94755 q = 1) : d150739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d150739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d150739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d94755 q = 1) : d150740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d150740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d150740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d94755 q = 1) : d150741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d150741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d150741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12987 q = 1) (hb : d94755 q = 1) : d150742 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12987, d150742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12987, d150742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29175 (p : Pattern) (ha : d12990 p = 1) (hb : d94755 p = 1) : d150745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d94755 q = 1) : d150731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29170 q ha hb
    | true =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d94755 q = 1) : d150732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d94755 q = 1) : d150733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d94755 q = 1) : d150734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d94755 q = 1) : d150735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d150735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d150735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12990 q = 1) (hb : d94755 q = 1) : d150745 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12990, d150745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12990, d150745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29176 (p : Pattern) (ha : d12991 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12991 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29177 (p : Pattern) (ha : d12997 p = 1) (hb : d94755 p = 1) : d150751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d94755 q = 1) : d150737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d150737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29172 q ha hb
    | true =>
      simp only [d12982, d150737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29173 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d94755 q = 1) : d150738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d150738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d150738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d94755 q = 1) : d150739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d150739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d150739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d94755 q = 1) : d150740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d150740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d150740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d94755 q = 1) : d150741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d150741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d150741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12992 q = 1) (hb : d94755 q = 1) : d150746 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d150746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29175 q ha hb
    | true =>
      simp only [d12992, d150746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29176 q ha hb
  have h7 (q : Pattern) (ha : d12993 q = 1) (hb : d94755 q = 1) : d150747 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d150747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d150747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12994 q = 1) (hb : d94755 q = 1) : d150748 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d150748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12994, d150748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12995 q = 1) (hb : d94755 q = 1) : d150749 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d150749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d150749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12996 q = 1) (hb : d94755 q = 1) : d150750 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d150750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d150750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12997 q = 1) (hb : d94755 q = 1) : d150751 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12997, d150751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12997, d150751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29178 (p : Pattern) (ha : d13040 p = 1) (hb : d94755 p = 1) : d150730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12959 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5026 q = 1) (hb : d94753 q = 1) : d5026 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12960 q = 1) (hb : d94755 q = 1) : d150728 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d94755, d150728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12960, d94755, d150728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5026 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5027 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d5027, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13039 q = 1) (hb : d94755 q = 1) : d150729 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13039, d150729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13039, d150729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13040 q = 1) (hb : d94755 q = 1) : d150730 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13040, d150730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13040, d150730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29179 (p : Pattern) (ha : d13050 p = 1) (hb : d94755 p = 1) : d150736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d94755 q = 1) : d150731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29178 q ha hb
    | true =>
      simp only [d13041, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d94755 q = 1) : d150732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d94755 q = 1) : d150733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d94755 q = 1) : d150734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d94755 q = 1) : d150735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d150735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d150735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13050 q = 1) (hb : d94755 q = 1) : d150736 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13050, d150736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13050, d150736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29180 (p : Pattern) (ha : d13134 p = 1) (hb : d94755 p = 1) : d150801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13124 q = 1) (hb : d94755 q = 1) : d150737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13124, d150737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29179 q ha hb
    | true =>
      simp only [d13124, d150737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29173 q ha hb
  have h2 (q : Pattern) (ha : d13125 q = 1) (hb : d94755 q = 1) : d150738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13125, d150738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13125, d150738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13126 q = 1) (hb : d94755 q = 1) : d150739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13126, d150739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13126, d150739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13127 q = 1) (hb : d94755 q = 1) : d150740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13127, d150740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13127, d150740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13128 q = 1) (hb : d94755 q = 1) : d150741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13128, d150741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13128, d150741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13129 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29173 q ha hb
    | true =>
      simp only [d13129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13130 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13131 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13132 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13133 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13134 q = 1) (hb : d94755 q = 1) : d150801 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13134, d150801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13134, d150801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29181 (p : Pattern) (ha : d13140 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13129 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29173 q ha hb
    | true =>
      simp only [d13129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13130 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13131 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13132 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13133 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13135 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29176 q ha hb
    | true =>
      simp only [d13135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13136 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13137 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13138 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13139 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13140 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29182 (p : Pattern) (ha : d13149 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13135 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29176 q ha hb
    | true =>
      simp only [d13135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13136 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13137 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13138 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13139 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13149 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29183 (p : Pattern) (ha : d13196 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13193 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13194 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13194, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13195 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13196 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro29184 (p : Pattern) (ha : d13260 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13197 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29183 q ha hb
    | true =>
      simp only [d13197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13198 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13257 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13258 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13259 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13260 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29185 (p : Pattern) (ha : d13266 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13261 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29184 q ha hb
    | true =>
      simp only [d13261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13262 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13263 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13264 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13265 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13266 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29186 (p : Pattern) (ha : d13002 p = 1) (hb : d94755 p = 1) : d150756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d94755 q = 1) : d150731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29170 q ha hb
    | true =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d94755 q = 1) : d150732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d94755 q = 1) : d150733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d94755 q = 1) : d150734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d94755 q = 1) : d150755 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d150755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d150755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13002 q = 1) (hb : d94755 q = 1) : d150756 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13002, d150756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13002, d150756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29187 (p : Pattern) (ha : d13004 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13004 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29188 (p : Pattern) (ha : d13011 p = 1) (hb : d94755 p = 1) : d150763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d94755 q = 1) : d150731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29170 q ha hb
    | true =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d94755 q = 1) : d150732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d94755 q = 1) : d150733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d94755 q = 1) : d150761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d150761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d150761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d94755 q = 1) : d150762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d150762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d150762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13011 q = 1) (hb : d94755 q = 1) : d150763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13011, d150763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13011, d150763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29189 (p : Pattern) (ha : d13014 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13014 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29190 (p : Pattern) (ha : d13036 p = 1) (hb : d94755 p = 1) : d150769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13021 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13033 q = 1) (hb : d94753 q = 1) : d13033 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13034 q = 1) (hb : d94755 q = 1) : d150767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13034, d94755, d150767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13034, d94755, d150767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12959 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5026 q = 1) (hb : d94753 q = 1) : d5026 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12960 q = 1) (hb : d94755 q = 1) : d150728 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d94755, d150728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d12960, d94755, d150728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13035 q = 1) (hb : d94755 q = 1) : d150768 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13035, d150768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13035, d150768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13036 q = 1) (hb : d94755 q = 1) : d150769 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13036, d150769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13036, d150769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29191 (p : Pattern) (ha : d13046 p = 1) (hb : d94755 p = 1) : d150775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d94755 q = 1) : d150770 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d150770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29190 q ha hb
    | true =>
      simp only [d13037, d150770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d94755 q = 1) : d150771 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d150771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d150771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d94755 q = 1) : d150731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29178 q ha hb
    | true =>
      simp only [d13041, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d94755 q = 1) : d150732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d94755 q = 1) : d150772 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d150772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d150772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d94755 q = 1) : d150773 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d150773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d150773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d94755 q = 1) : d150774 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d150774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d150774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13046 q = 1) (hb : d94755 q = 1) : d150775 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13046, d150775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13046, d150775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29192 (p : Pattern) (ha : d13091 p = 1) (hb : d94755 p = 1) : d150736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d94755 q = 1) : d150731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29170 q ha hb
    | true =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d94755 q = 1) : d150732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d94755 q = 1) : d150733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d94755 q = 1) : d150734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d94755 q = 1) : d150735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d150735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d150735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13091 q = 1) (hb : d94755 q = 1) : d150736 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13091, d150736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13091, d150736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29193 (p : Pattern) (ha : d94755 p = 1) (hb : d115400 p = 1) : d150782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d94755 q = 1) : d150757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d150757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29186 q ha hb
    | true =>
      simp only [d13005, d150757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29187 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d94755 q = 1) : d150758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d150758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d150758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d94755 q = 1) : d150759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d150759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d150759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d94755 q = 1) : d150760 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d150760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d150760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d94755 q = 1) : d150764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d150764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29188 q ha hb
    | true =>
      simp only [d13015, d150764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29189 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d94755 q = 1) : d150765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d150765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d150765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d94755 q = 1) : d150766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d150766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d150766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d94755 q = 1) : d150776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d150776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29191 q ha hb
    | true =>
      simp only [d13051, d150776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29179 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115396 q = 1) : d150777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d150777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115396, d150777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d94755 q = 1) : d150737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d150737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29192 q ha hb
    | true =>
      simp only [d13092, d150737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d94755 q = 1) : d150778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d150778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d150778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115397 q = 1) : d150779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d150779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d150779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115398 q = 1) : d150780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d150780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115398, d150780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115399 q = 1) : d150781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d150781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115399, d150781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115400 q = 1) : d150782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115400, d150782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115400, d150782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29194 (p : Pattern) (ha : d13098 p = 1) (hb : d94755 p = 1) : d150783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d94755 q = 1) : d150731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29170 q ha hb
    | true =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d94755 q = 1) : d150732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d94755 q = 1) : d150733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d94755 q = 1) : d150734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d94755 q = 1) : d150755 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d150755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d150755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13098 q = 1) (hb : d94755 q = 1) : d150783 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13098, d150783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13098, d150783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29195 (p : Pattern) (ha : d13099 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13099 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29196 (p : Pattern) (ha : d13104 p = 1) (hb : d94755 p = 1) : d150788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d94755 q = 1) : d150731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29170 q ha hb
    | true =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d94755 q = 1) : d150732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d94755 q = 1) : d150733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d94755 q = 1) : d150761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d150761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d150761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d94755 q = 1) : d150762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d150762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d150762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13104 q = 1) (hb : d94755 q = 1) : d150788 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13104, d150788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13104, d150788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29197 (p : Pattern) (ha : d13105 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13105 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29198 (p : Pattern) (ha : d13109 p = 1) (hb : d94755 p = 1) : d150792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d94755 q = 1) : d150770 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d150770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29190 q ha hb
    | true =>
      simp only [d13037, d150770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d94755 q = 1) : d150771 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d150771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d150771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d94755 q = 1) : d150731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29178 q ha hb
    | true =>
      simp only [d13041, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d94755 q = 1) : d150732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d94755 q = 1) : d150772 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d150772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d150772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d94755 q = 1) : d150773 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d150773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d150773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d94755 q = 1) : d150774 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d150774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d150774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13109 q = 1) (hb : d94755 q = 1) : d150792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13109, d150792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13109, d150792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29199 (p : Pattern) (ha : d13110 p = 1) (hb : d94755 p = 1) : d150745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d94755 q = 1) : d150731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29178 q ha hb
    | true =>
      simp only [d13041, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d94755 q = 1) : d150732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29171 q ha hb
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d94755 q = 1) : d150733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d94755 q = 1) : d150734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d94755 q = 1) : d150735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d150735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d150735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13110 q = 1) (hb : d94755 q = 1) : d150745 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13110, d150745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13110, d150745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29200 (p : Pattern) (ha : d13116 p = 1) (hb : d94755 p = 1) : d150745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d94755 q = 1) : d150731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29170 q ha hb
    | true =>
      simp only [d12968, d150731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d94755 q = 1) : d150732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d150732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d94755 q = 1) : d150733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d150733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d94755 q = 1) : d150734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d150734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d94755 q = 1) : d150735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d150735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d150735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13116 q = 1) (hb : d94755 q = 1) : d150745 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13116, d150745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13116, d150745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29201 (p : Pattern) (ha : d94755 p = 1) (hb : d115405 p = 1) : d150799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d94755 q = 1) : d150757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d150757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29186 q ha hb
    | true =>
      simp only [d13005, d150757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29187 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d94755 q = 1) : d150758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d150758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d150758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d94755 q = 1) : d150759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d150759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d150759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d94755 q = 1) : d150760 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d150760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d150760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d94755 q = 1) : d150764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d150764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29188 q ha hb
    | true =>
      simp only [d13015, d150764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29189 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d94755 q = 1) : d150765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d150765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d150765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d94755 q = 1) : d150766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d150766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d150766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d94755 q = 1) : d150776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d150776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29191 q ha hb
    | true =>
      simp only [d13051, d150776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29179 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115396 q = 1) : d150777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d150777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115396, d150777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d94755 q = 1) : d150737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d150737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29192 q ha hb
    | true =>
      simp only [d13092, d150737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d94755 q = 1) : d150778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d150778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d150778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115397 q = 1) : d150779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d150779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d150779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115398 q = 1) : d150780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d150780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115398, d150780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115399 q = 1) : d150781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d150781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115399, d150781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13100 q = 1) (hb : d94755 q = 1) : d150784 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13100, d150784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29194 q ha hb
    | true =>
      simp only [d13100, d150784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29195 q ha hb
  have h16 (q : Pattern) (ha : d13101 q = 1) (hb : d94755 q = 1) : d150785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13101, d150785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13101, d150785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13102 q = 1) (hb : d94755 q = 1) : d150786 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13102, d150786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13102, d150786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13103 q = 1) (hb : d94755 q = 1) : d150787 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13103, d150787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13103, d150787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13106 q = 1) (hb : d94755 q = 1) : d150789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13106, d150789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29196 q ha hb
    | true =>
      simp only [d13106, d150789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29197 q ha hb
  have h20 (q : Pattern) (ha : d13107 q = 1) (hb : d94755 q = 1) : d150790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13107, d150790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13107, d150790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13108 q = 1) (hb : d94755 q = 1) : d150791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13108, d150791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13108, d150791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13111 q = 1) (hb : d94755 q = 1) : d150793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d150793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29198 q ha hb
    | true =>
      simp only [d13111, d150793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29199 q ha hb
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115401 q = 1) : d150794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d150794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d115401, d150794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d13117 q = 1) (hb : d94755 q = 1) : d150746 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d150746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29200 q ha hb
    | true =>
      simp only [d13117, d150746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13118 q = 1) (hb : d94755 q = 1) : d150795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d150795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13118, d150795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94755 q = 1) (hb : d115402 q = 1) : d150796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d150796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115402, d150796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d94755 q = 1) (hb : d115403 q = 1) : d150797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115403, d150797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115403, d150797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94755 q = 1) (hb : d115404 q = 1) : d150798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115404, d150798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d115404, d150798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94755 q = 1) (hb : d115405 q = 1) : d150799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115405, d150799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115405, d150799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro29202 (p : Pattern) (ha : d94755 p = 1) (hb : d115412 p = 1) : d150808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13111 q = 1) (hb : d94755 q = 1) : d150793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d150793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29198 q ha hb
    | true =>
      simp only [d13111, d150793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29199 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115401 q = 1) : d150794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d150794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115401, d150794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d13117 q = 1) (hb : d94755 q = 1) : d150746 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d150746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29200 q ha hb
    | true =>
      simp only [d13117, d150746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13118 q = 1) (hb : d94755 q = 1) : d150795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d150795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13118, d150795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115402 q = 1) : d150796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d150796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115402, d150796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115410 q = 1) : d150806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115410, d150806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115410, d150806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115411 q = 1) : d150807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115411, d150807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115411, d150807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115412 q = 1) : d150808 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115412, d150808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115412, d150808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29203 (p : Pattern) (ha : d13179 p = 1) (hb : d94755 p = 1) : d150817 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13159 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13172 q = 1) (hb : d94753 q = 1) : d13172 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13173 q = 1) (hb : d94755 q = 1) : d150814 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13173, d94755, d150814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13173, d94755, d150814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13176 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6358 q = 1) (hb : d94753 q = 1) : d6358 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13177 q = 1) (hb : d94755 q = 1) : d150815 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d94755, d150815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d13177, d94755, d150815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13178 q = 1) (hb : d94755 q = 1) : d150816 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13178, d150816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13178, d150816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13179 q = 1) (hb : d94755 q = 1) : d150817 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13179, d150817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13179, d150817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29204 (p : Pattern) (ha : d13183 p = 1) (hb : d94755 p = 1) : d150821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13176 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6358 q = 1) (hb : d94753 q = 1) : d6358 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13177 q = 1) (hb : d94755 q = 1) : d150815 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d94755, d150815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13177, d94755, d150815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6358 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6359 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d6359, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13182 q = 1) (hb : d94755 q = 1) : d150820 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13182, d150820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13182, d150820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13183 q = 1) (hb : d94755 q = 1) : d150821 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13183, d150821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13183, d150821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29205 (p : Pattern) (ha : d13189 p = 1) (hb : d94755 p = 1) : d150827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13180 q = 1) (hb : d94755 q = 1) : d150818 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13180, d150818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29203 q ha hb
    | true =>
      simp only [d13180, d150818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13181 q = 1) (hb : d94755 q = 1) : d150819 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13181, d150819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13181, d150819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13184 q = 1) (hb : d94755 q = 1) : d150822 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d150822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29204 q ha hb
    | true =>
      simp only [d13184, d150822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13185 q = 1) (hb : d94755 q = 1) : d150823 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d150823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d150823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13186 q = 1) (hb : d94755 q = 1) : d150824 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13186, d150824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13186, d150824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13187 q = 1) (hb : d94755 q = 1) : d150825 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13187, d150825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13187, d150825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13188 q = 1) (hb : d94755 q = 1) : d150826 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13188, d150826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13188, d150826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13189 q = 1) (hb : d94755 q = 1) : d150827 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13189, d150827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13189, d150827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29206 (p : Pattern) (ha : d13202 p = 1) (hb : d94755 p = 1) : d150831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13184 q = 1) (hb : d94755 q = 1) : d150822 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d150822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29204 q ha hb
    | true =>
      simp only [d13184, d150822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13185 q = 1) (hb : d94755 q = 1) : d150823 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d150823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d150823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29183 q ha hb
    | true =>
      simp only [d13197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13199 q = 1) (hb : d94755 q = 1) : d150828 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13199, d150828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13199, d150828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13200 q = 1) (hb : d94755 q = 1) : d150829 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13200, d150829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13200, d150829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13201 q = 1) (hb : d94755 q = 1) : d150830 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13201, d150830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13201, d150830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13202 q = 1) (hb : d94755 q = 1) : d150831 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13202, d150831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13202, d150831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29207 (p : Pattern) (ha : d13243 p = 1) (hb : d94755 p = 1) : d150821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13176 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6358 q = 1) (hb : d94753 q = 1) : d6358 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13177 q = 1) (hb : d94755 q = 1) : d150815 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d94755, d150815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13177, d94755, d150815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13193 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13194 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d13194, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13242 q = 1) (hb : d94755 q = 1) : d150820 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13242, d150820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13242, d150820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13243 q = 1) (hb : d94755 q = 1) : d150821 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13243, d150821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13243, d150821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29208 (p : Pattern) (ha : d13249 p = 1) (hb : d94755 p = 1) : d150831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d94755 q = 1) : d150822 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d150822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29207 q ha hb
    | true =>
      simp only [d13244, d150822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d94755 q = 1) : d150823 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d150823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d150823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13246 q = 1) (hb : d94755 q = 1) : d150828 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13246, d150828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13246, d150828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13247 q = 1) (hb : d94755 q = 1) : d150829 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13247, d150829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13247, d150829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13248 q = 1) (hb : d94755 q = 1) : d150830 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13248, d150830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13248, d150830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13249 q = 1) (hb : d94755 q = 1) : d150831 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13249, d150831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13249, d150831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29209 (p : Pattern) (ha : d94755 p = 1) (hb : d115422 p = 1) : d150839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13203 q = 1) (hb : d94755 q = 1) : d150832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13203, d150832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29205 q ha hb
    | true =>
      simp only [d13203, d150832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29206 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115418 q = 1) : d150833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115418, d150833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115418, d150833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d13250 q = 1) (hb : d94755 q = 1) : d150834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13250, d150834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29208 q ha hb
    | true =>
      simp only [d13250, d150834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13251 q = 1) (hb : d94755 q = 1) : d150835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13251, d150835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13251, d150835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115419 q = 1) : d150836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115419, d150836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115419, d150836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115420 q = 1) : d150837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115420, d150837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115420, d150837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115421 q = 1) : d150838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115421, d150838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115421, d150838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115422 q = 1) : d150839 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115422, d150839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115422, d150839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29210 (p : Pattern) (ha : d94755 p = 1) (hb : d115428 p = 1) : d150845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12988 q = 1) (hb : d94755 q = 1) : d150743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12988, d150743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12988, d150743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29174 q ha hb
  have h2 (q : Pattern) (ha : d12989 q = 1) (hb : d94755 q = 1) : d150744 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12989, d150744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12989, d150744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12998 q = 1) (hb : d94755 q = 1) : d150752 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d150752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29174 q ha hb
    | true =>
      simp only [d12998, d150752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29177 q ha hb
  have h4 (q : Pattern) (ha : d12999 q = 1) (hb : d94755 q = 1) : d150753 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d150753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12999, d150753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13000 q = 1) (hb : d94755 q = 1) : d150754 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13000, d150754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13000, d150754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115406 q = 1) : d150800 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115406, d150800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29193 q ha hb
    | true =>
      simp only [d115406, d150800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29201 q ha hb
  have h7 (q : Pattern) (ha : d13141 q = 1) (hb : d94755 q = 1) : d150802 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13141, d150802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29180 q ha hb
    | true =>
      simp only [d13141, d150802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29181 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115407 q = 1) : d150803 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115407, d150803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115407, d150803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115408 q = 1) : d150804 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115408, d150804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115408, d150804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d115409 q = 1) : d150805 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115409, d150805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115409, d150805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d115413 q = 1) : d150809 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115413, d150809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115413, d150809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29202 q ha hb
  have h12 (q : Pattern) (ha : d13150 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29182 q ha hb
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115414 q = 1) : d150810 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115414, d150810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115414, d150810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115415 q = 1) : d150811 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115415, d150811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115415, d150811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115416 q = 1) : d150812 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115416, d150812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115416, d150812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d94755 q = 1) (hb : d115417 q = 1) : d150813 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115417, d150813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115417, d150813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94755 q = 1) (hb : d115423 q = 1) : d150840 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115423, d150840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115423, d150840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29209 q ha hb
  have h18 (q : Pattern) (ha : d13267 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29185 q ha hb
  have h19 (q : Pattern) (ha : d94755 q = 1) (hb : d115424 q = 1) : d150841 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115424, d150841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115424, d150841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d94755 q = 1) (hb : d115425 q = 1) : d150842 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115425, d150842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115425, d150842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d94755 q = 1) (hb : d115426 q = 1) : d150843 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115426, d150843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115426, d150843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d94755 q = 1) (hb : d115427 q = 1) : d150844 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115427, d150844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115427, d150844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115428 q = 1) : d150845 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115428, d150845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115428, d150845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29211 (p : Pattern) (ha : d94755 p = 1) (hb : d115434 p = 1) : d150851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d115429 q = 1) : d150846 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115429, d150846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115429, d150846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29210 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115430 q = 1) : d150847 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115430, d150847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115430, d150847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d115431 q = 1) : d150848 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115431, d150848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115431, d150848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d115432 q = 1) : d150849 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115432, d150849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115432, d150849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115433 q = 1) : d150850 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115433, d150850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115433, d150850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115434 q = 1) : d150851 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115434, d150851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115434, d150851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29212 (p : Pattern) (ha : d13293 p = 1) (hb : d94755 p = 1) : d150857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13285 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5142 q = 1) (hb : d94753 q = 1) : d5142 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13286 q = 1) (hb : d94755 q = 1) : d150855 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d94755, d150855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13286, d94755, d150855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13290 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13291 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d13291, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13292 q = 1) (hb : d94755 q = 1) : d150856 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13292, d150856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13292, d150856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13293 q = 1) (hb : d94755 q = 1) : d150857 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13293, d150857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13293, d150857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29213 (p : Pattern) (ha : d13297 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13290 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13291 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13291, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13296 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13297 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro29214 (p : Pattern) (ha : d13303 p = 1) (hb : d94755 p = 1) : d150863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d94755 q = 1) : d150858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29212 q ha hb
    | true =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d94755 q = 1) : d150859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d94755 q = 1) : d150860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d94755 q = 1) : d150861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d94755 q = 1) : d150862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d150862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d150862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13303 q = 1) (hb : d94755 q = 1) : d150863 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13303, d150863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13303, d150863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29215 (p : Pattern) (ha : d13307 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13307 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29216 (p : Pattern) (ha : d13313 p = 1) (hb : d94755 p = 1) : d150869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d94755 q = 1) : d150864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d150864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29214 q ha hb
    | true =>
      simp only [d13308, d150864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29215 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d94755 q = 1) : d150865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d150865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d150865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d94755 q = 1) : d150866 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d150866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d150866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d94755 q = 1) : d150867 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d150867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d150867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d94755 q = 1) : d150868 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d150868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d150868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13313 q = 1) (hb : d94755 q = 1) : d150869 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13313, d150869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13313, d150869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29217 (p : Pattern) (ha : d13316 p = 1) (hb : d94755 p = 1) : d150872 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d94755 q = 1) : d150858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29212 q ha hb
    | true =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d94755 q = 1) : d150859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d94755 q = 1) : d150860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d94755 q = 1) : d150861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d94755 q = 1) : d150862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d150862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d150862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13316 q = 1) (hb : d94755 q = 1) : d150872 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13316, d150872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13316, d150872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29218 (p : Pattern) (ha : d13317 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13317 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29219 (p : Pattern) (ha : d13323 p = 1) (hb : d94755 p = 1) : d150878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d94755 q = 1) : d150864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d150864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29214 q ha hb
    | true =>
      simp only [d13308, d150864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29215 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d94755 q = 1) : d150865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d150865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d150865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d94755 q = 1) : d150866 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d150866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d150866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d94755 q = 1) : d150867 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d150867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d150867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d94755 q = 1) : d150868 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d150868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d150868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13318 q = 1) (hb : d94755 q = 1) : d150873 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d150873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29217 q ha hb
    | true =>
      simp only [d13318, d150873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29218 q ha hb
  have h7 (q : Pattern) (ha : d13319 q = 1) (hb : d94755 q = 1) : d150874 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d150874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d150874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13320 q = 1) (hb : d94755 q = 1) : d150875 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d150875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13320, d150875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13321 q = 1) (hb : d94755 q = 1) : d150876 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d150876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d150876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13322 q = 1) (hb : d94755 q = 1) : d150877 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d150877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d150877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13323 q = 1) (hb : d94755 q = 1) : d150878 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13323, d150878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13323, d150878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29220 (p : Pattern) (ha : d13366 p = 1) (hb : d94755 p = 1) : d150857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13285 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5142 q = 1) (hb : d94753 q = 1) : d5142 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13286 q = 1) (hb : d94755 q = 1) : d150855 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d94755, d150855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13286, d94755, d150855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5142 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5143 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d5143, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13365 q = 1) (hb : d94755 q = 1) : d150856 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13365, d150856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13365, d150856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13366 q = 1) (hb : d94755 q = 1) : d150857 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13366, d150857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13366, d150857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29221 (p : Pattern) (ha : d13376 p = 1) (hb : d94755 p = 1) : d150863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d94755 q = 1) : d150858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29220 q ha hb
    | true =>
      simp only [d13367, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d94755 q = 1) : d150859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13373 q = 1) (hb : d94755 q = 1) : d150860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13374 q = 1) (hb : d94755 q = 1) : d150861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13374, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13375 q = 1) (hb : d94755 q = 1) : d150862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d150862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13375, d150862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13376 q = 1) (hb : d94755 q = 1) : d150863 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13376, d150863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13376, d150863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29222 (p : Pattern) (ha : d13460 p = 1) (hb : d94755 p = 1) : d150928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13450 q = 1) (hb : d94755 q = 1) : d150864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13450, d150864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29221 q ha hb
    | true =>
      simp only [d13450, d150864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29215 q ha hb
  have h2 (q : Pattern) (ha : d13451 q = 1) (hb : d94755 q = 1) : d150865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13451, d150865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13451, d150865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13452 q = 1) (hb : d94755 q = 1) : d150866 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13452, d150866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13452, d150866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13453 q = 1) (hb : d94755 q = 1) : d150867 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13453, d150867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13453, d150867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13454 q = 1) (hb : d94755 q = 1) : d150868 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13454, d150868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13454, d150868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13455 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29215 q ha hb
    | true =>
      simp only [d13455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13456 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13457 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13458 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13459 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13460 q = 1) (hb : d94755 q = 1) : d150928 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13460, d150928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13460, d150928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29223 (p : Pattern) (ha : d13466 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13455 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29215 q ha hb
    | true =>
      simp only [d13455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13456 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13457 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13458 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13459 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13461 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29218 q ha hb
    | true =>
      simp only [d13461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13462 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13463 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13464 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13465 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13466 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29224 (p : Pattern) (ha : d13475 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13461 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29218 q ha hb
    | true =>
      simp only [d13461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13462 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13463 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13464 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13465 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13475 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29225 (p : Pattern) (ha : d13522 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13519 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13520 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13520, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13521 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13522 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro29226 (p : Pattern) (ha : d13586 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13523 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29225 q ha hb
    | true =>
      simp only [d13523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13524 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13583 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13584 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13585 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13586 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29227 (p : Pattern) (ha : d13592 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13587 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29226 q ha hb
    | true =>
      simp only [d13587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13588 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13589 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13590 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13591 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13592 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29228 (p : Pattern) (ha : d13328 p = 1) (hb : d94755 p = 1) : d150883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d94755 q = 1) : d150858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29212 q ha hb
    | true =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d94755 q = 1) : d150859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d94755 q = 1) : d150860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d94755 q = 1) : d150861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d94755 q = 1) : d150882 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d150882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d150882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13328 q = 1) (hb : d94755 q = 1) : d150883 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13328, d150883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13328, d150883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29229 (p : Pattern) (ha : d13330 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13330 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29230 (p : Pattern) (ha : d13337 p = 1) (hb : d94755 p = 1) : d150890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d94755 q = 1) : d150858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29212 q ha hb
    | true =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d94755 q = 1) : d150859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d94755 q = 1) : d150860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13335 q = 1) (hb : d94755 q = 1) : d150888 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d150888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d150888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13336 q = 1) (hb : d94755 q = 1) : d150889 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d150889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13336, d150889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13337 q = 1) (hb : d94755 q = 1) : d150890 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13337, d150890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13337, d150890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29231 (p : Pattern) (ha : d13340 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13340 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29232 (p : Pattern) (ha : d13362 p = 1) (hb : d94755 p = 1) : d150896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13347 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13359 q = 1) (hb : d94753 q = 1) : d13359 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13360 q = 1) (hb : d94755 q = 1) : d150894 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13360, d94755, d150894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13360, d94755, d150894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13285 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5142 q = 1) (hb : d94753 q = 1) : d5142 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13286 q = 1) (hb : d94755 q = 1) : d150855 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d94755, d150855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d13286, d94755, d150855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13361 q = 1) (hb : d94755 q = 1) : d150895 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13361, d150895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13361, d150895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13362 q = 1) (hb : d94755 q = 1) : d150896 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13362, d150896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13362, d150896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29233 (p : Pattern) (ha : d13372 p = 1) (hb : d94755 p = 1) : d150902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d94755 q = 1) : d150897 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d150897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29232 q ha hb
    | true =>
      simp only [d13363, d150897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d94755 q = 1) : d150898 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d150898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d150898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d94755 q = 1) : d150858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29220 q ha hb
    | true =>
      simp only [d13367, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d94755 q = 1) : d150859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d94755 q = 1) : d150899 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d150899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d150899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d94755 q = 1) : d150900 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d150900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d150900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d94755 q = 1) : d150901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d150901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d150901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13372 q = 1) (hb : d94755 q = 1) : d150902 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13372, d150902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13372, d150902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29234 (p : Pattern) (ha : d13417 p = 1) (hb : d94755 p = 1) : d150863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d94755 q = 1) : d150858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29212 q ha hb
    | true =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d94755 q = 1) : d150859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d94755 q = 1) : d150860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d94755 q = 1) : d150861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d94755 q = 1) : d150862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d150862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d150862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13417 q = 1) (hb : d94755 q = 1) : d150863 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13417, d150863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13417, d150863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29235 (p : Pattern) (ha : d94755 p = 1) (hb : d115442 p = 1) : d150909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13331 q = 1) (hb : d94755 q = 1) : d150884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d150884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29228 q ha hb
    | true =>
      simp only [d13331, d150884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29229 q ha hb
  have h2 (q : Pattern) (ha : d13332 q = 1) (hb : d94755 q = 1) : d150885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d150885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d150885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13333 q = 1) (hb : d94755 q = 1) : d150886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d150886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13333, d150886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13334 q = 1) (hb : d94755 q = 1) : d150887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d150887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d150887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13341 q = 1) (hb : d94755 q = 1) : d150891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d150891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29230 q ha hb
    | true =>
      simp only [d13341, d150891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29231 q ha hb
  have h6 (q : Pattern) (ha : d13342 q = 1) (hb : d94755 q = 1) : d150892 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d150892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d150892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13343 q = 1) (hb : d94755 q = 1) : d150893 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d150893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13343, d150893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13377 q = 1) (hb : d94755 q = 1) : d150903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d150903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29233 q ha hb
    | true =>
      simp only [d13377, d150903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29221 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115438 q = 1) : d150904 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d150904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115438, d150904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d13418 q = 1) (hb : d94755 q = 1) : d150864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d150864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29234 q ha hb
    | true =>
      simp only [d13418, d150864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13419 q = 1) (hb : d94755 q = 1) : d150905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d150905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13419, d150905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115439 q = 1) : d150906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d150906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115439, d150906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115440 q = 1) : d150907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d150907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115440, d150907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115441 q = 1) : d150908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d150908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115441, d150908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115442 q = 1) : d150909 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115442, d150909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115442, d150909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29236 (p : Pattern) (ha : d13424 p = 1) (hb : d94755 p = 1) : d150910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d94755 q = 1) : d150858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29212 q ha hb
    | true =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d94755 q = 1) : d150859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d94755 q = 1) : d150860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d94755 q = 1) : d150861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d94755 q = 1) : d150882 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d150882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d150882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13424 q = 1) (hb : d94755 q = 1) : d150910 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13424, d150910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13424, d150910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29237 (p : Pattern) (ha : d13425 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13425 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29238 (p : Pattern) (ha : d13430 p = 1) (hb : d94755 p = 1) : d150915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d94755 q = 1) : d150858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29212 q ha hb
    | true =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d94755 q = 1) : d150859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d94755 q = 1) : d150860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13335 q = 1) (hb : d94755 q = 1) : d150888 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d150888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d150888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13336 q = 1) (hb : d94755 q = 1) : d150889 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d150889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13336, d150889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13430 q = 1) (hb : d94755 q = 1) : d150915 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13430, d150915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13430, d150915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29239 (p : Pattern) (ha : d13431 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13431 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29240 (p : Pattern) (ha : d13435 p = 1) (hb : d94755 p = 1) : d150919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d94755 q = 1) : d150897 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d150897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29232 q ha hb
    | true =>
      simp only [d13363, d150897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d94755 q = 1) : d150898 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d150898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d150898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d94755 q = 1) : d150858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29220 q ha hb
    | true =>
      simp only [d13367, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d94755 q = 1) : d150859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d94755 q = 1) : d150899 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d150899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d150899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d94755 q = 1) : d150900 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d150900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d150900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d94755 q = 1) : d150901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d150901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d150901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13435 q = 1) (hb : d94755 q = 1) : d150919 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13435, d150919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13435, d150919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29241 (p : Pattern) (ha : d13436 p = 1) (hb : d94755 p = 1) : d150872 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d94755 q = 1) : d150858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29220 q ha hb
    | true =>
      simp only [d13367, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d94755 q = 1) : d150859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29213 q ha hb
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13373 q = 1) (hb : d94755 q = 1) : d150860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13374 q = 1) (hb : d94755 q = 1) : d150861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13374, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13375 q = 1) (hb : d94755 q = 1) : d150862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d150862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13375, d150862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13436 q = 1) (hb : d94755 q = 1) : d150872 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13436, d150872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13436, d150872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29242 (p : Pattern) (ha : d13442 p = 1) (hb : d94755 p = 1) : d150872 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d94755 q = 1) : d150858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29212 q ha hb
    | true =>
      simp only [d13294, d150858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d94755 q = 1) : d150859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d150859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d94755 q = 1) : d150860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d150860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d94755 q = 1) : d150861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d150861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d94755 q = 1) : d150862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d150862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d150862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13442 q = 1) (hb : d94755 q = 1) : d150872 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13442, d150872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13442, d150872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29243 (p : Pattern) (ha : d94755 p = 1) (hb : d115447 p = 1) : d150926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13331 q = 1) (hb : d94755 q = 1) : d150884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d150884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29228 q ha hb
    | true =>
      simp only [d13331, d150884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29229 q ha hb
  have h2 (q : Pattern) (ha : d13332 q = 1) (hb : d94755 q = 1) : d150885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d150885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d150885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13333 q = 1) (hb : d94755 q = 1) : d150886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d150886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13333, d150886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13334 q = 1) (hb : d94755 q = 1) : d150887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d150887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d150887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13341 q = 1) (hb : d94755 q = 1) : d150891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d150891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29230 q ha hb
    | true =>
      simp only [d13341, d150891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29231 q ha hb
  have h6 (q : Pattern) (ha : d13342 q = 1) (hb : d94755 q = 1) : d150892 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d150892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d150892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13343 q = 1) (hb : d94755 q = 1) : d150893 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d150893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13343, d150893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13377 q = 1) (hb : d94755 q = 1) : d150903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d150903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29233 q ha hb
    | true =>
      simp only [d13377, d150903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29221 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115438 q = 1) : d150904 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d150904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115438, d150904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d13418 q = 1) (hb : d94755 q = 1) : d150864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d150864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29234 q ha hb
    | true =>
      simp only [d13418, d150864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13419 q = 1) (hb : d94755 q = 1) : d150905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d150905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13419, d150905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115439 q = 1) : d150906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d150906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115439, d150906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115440 q = 1) : d150907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d150907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115440, d150907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115441 q = 1) : d150908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d150908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115441, d150908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13426 q = 1) (hb : d94755 q = 1) : d150911 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13426, d150911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29236 q ha hb
    | true =>
      simp only [d13426, d150911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29237 q ha hb
  have h16 (q : Pattern) (ha : d13427 q = 1) (hb : d94755 q = 1) : d150912 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13427, d150912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13427, d150912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13428 q = 1) (hb : d94755 q = 1) : d150913 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13428, d150913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13428, d150913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13429 q = 1) (hb : d94755 q = 1) : d150914 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13429, d150914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13429, d150914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13432 q = 1) (hb : d94755 q = 1) : d150916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13432, d150916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29238 q ha hb
    | true =>
      simp only [d13432, d150916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29239 q ha hb
  have h20 (q : Pattern) (ha : d13433 q = 1) (hb : d94755 q = 1) : d150917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13433, d150917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13433, d150917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13434 q = 1) (hb : d94755 q = 1) : d150918 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13434, d150918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13434, d150918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13437 q = 1) (hb : d94755 q = 1) : d150920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d150920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29240 q ha hb
    | true =>
      simp only [d13437, d150920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29241 q ha hb
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115443 q = 1) : d150921 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d150921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d115443, d150921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d13443 q = 1) (hb : d94755 q = 1) : d150873 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d150873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29242 q ha hb
    | true =>
      simp only [d13443, d150873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13444 q = 1) (hb : d94755 q = 1) : d150922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d150922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13444, d150922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94755 q = 1) (hb : d115444 q = 1) : d150923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d150923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115444, d150923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d94755 q = 1) (hb : d115445 q = 1) : d150924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115445, d150924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115445, d150924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94755 q = 1) (hb : d115446 q = 1) : d150925 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115446, d150925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d115446, d150925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94755 q = 1) (hb : d115447 q = 1) : d150926 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115447, d150926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115447, d150926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro29244 (p : Pattern) (ha : d94755 p = 1) (hb : d115454 p = 1) : d150935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13437 q = 1) (hb : d94755 q = 1) : d150920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d150920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29240 q ha hb
    | true =>
      simp only [d13437, d150920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29241 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115443 q = 1) : d150921 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d150921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115443, d150921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d13443 q = 1) (hb : d94755 q = 1) : d150873 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d150873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29242 q ha hb
    | true =>
      simp only [d13443, d150873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13444 q = 1) (hb : d94755 q = 1) : d150922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d150922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13444, d150922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115444 q = 1) : d150923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d150923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115444, d150923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115452 q = 1) : d150933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115452, d150933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115452, d150933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115453 q = 1) : d150934 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115453, d150934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115453, d150934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115454 q = 1) : d150935 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115454, d150935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115454, d150935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29245 (p : Pattern) (ha : d13505 p = 1) (hb : d94755 p = 1) : d150944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13485 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13498 q = 1) (hb : d94753 q = 1) : d13498 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13499 q = 1) (hb : d94755 q = 1) : d150941 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13499, d94755, d150941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13499, d94755, d150941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13502 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6504 q = 1) (hb : d94753 q = 1) : d6504 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13503 q = 1) (hb : d94755 q = 1) : d150942 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d94755, d150942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d13503, d94755, d150942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13504 q = 1) (hb : d94755 q = 1) : d150943 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13504, d150943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13504, d150943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13505 q = 1) (hb : d94755 q = 1) : d150944 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13505, d150944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13505, d150944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29246 (p : Pattern) (ha : d13509 p = 1) (hb : d94755 p = 1) : d150948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13502 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6504 q = 1) (hb : d94753 q = 1) : d6504 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13503 q = 1) (hb : d94755 q = 1) : d150942 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d94755, d150942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13503, d94755, d150942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6504 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6505 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d6505, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13508 q = 1) (hb : d94755 q = 1) : d150947 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13508, d150947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13508, d150947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13509 q = 1) (hb : d94755 q = 1) : d150948 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13509, d150948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13509, d150948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29247 (p : Pattern) (ha : d13515 p = 1) (hb : d94755 p = 1) : d150954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13506 q = 1) (hb : d94755 q = 1) : d150945 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13506, d150945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29245 q ha hb
    | true =>
      simp only [d13506, d150945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13507 q = 1) (hb : d94755 q = 1) : d150946 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13507, d150946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13507, d150946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13510 q = 1) (hb : d94755 q = 1) : d150949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d150949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29246 q ha hb
    | true =>
      simp only [d13510, d150949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13511 q = 1) (hb : d94755 q = 1) : d150950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d150950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d150950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13512 q = 1) (hb : d94755 q = 1) : d150951 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13512, d150951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13512, d150951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13513 q = 1) (hb : d94755 q = 1) : d150952 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13513, d150952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13513, d150952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13514 q = 1) (hb : d94755 q = 1) : d150953 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13514, d150953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13514, d150953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13515 q = 1) (hb : d94755 q = 1) : d150954 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13515, d150954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13515, d150954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29248 (p : Pattern) (ha : d13528 p = 1) (hb : d94755 p = 1) : d150958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13510 q = 1) (hb : d94755 q = 1) : d150949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d150949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29246 q ha hb
    | true =>
      simp only [d13510, d150949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13511 q = 1) (hb : d94755 q = 1) : d150950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d150950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d150950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29225 q ha hb
    | true =>
      simp only [d13523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13525 q = 1) (hb : d94755 q = 1) : d150955 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13525, d150955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13525, d150955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13526 q = 1) (hb : d94755 q = 1) : d150956 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13526, d150956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13526, d150956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13527 q = 1) (hb : d94755 q = 1) : d150957 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13527, d150957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13527, d150957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13528 q = 1) (hb : d94755 q = 1) : d150958 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13528, d150958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13528, d150958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29249 (p : Pattern) (ha : d13569 p = 1) (hb : d94755 p = 1) : d150948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13502 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6504 q = 1) (hb : d94753 q = 1) : d6504 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13503 q = 1) (hb : d94755 q = 1) : d150942 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d94755, d150942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13503, d94755, d150942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13519 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13520 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d13520, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13568 q = 1) (hb : d94755 q = 1) : d150947 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13568, d150947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13568, d150947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13569 q = 1) (hb : d94755 q = 1) : d150948 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13569, d150948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13569, d150948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
