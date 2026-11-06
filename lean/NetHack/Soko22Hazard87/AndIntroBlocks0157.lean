import NetHack.Soko22Hazard87.AndIntroBlocks0156
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro39250 (p : Pattern) (ha : d15985 p = 1) (hb : d174727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d174722 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d174722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39249 q ha hb
    | true =>
      simp only [d15973, d174722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d174723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d174723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d174723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d174688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d174688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39242 q ha hb
    | true =>
      simp only [d151, d174688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d174689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d174689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d174689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d174724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d174724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d174724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d174725 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d174725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d174725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d174726 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d174726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d174726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d174727 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d174727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d174727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39251 (p : Pattern) (ha : d128207 p = 1) (hb : d174739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d174728 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d174728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39250 q ha hb
    | true =>
      simp only [d15986, d174728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39243 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d174694 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128196 q = 1) (hb : d174729 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d174729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, d174729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5356 q = 1) (hb : d174734 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d174734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39247 q ha hb
    | true =>
      simp only [d5356, d174734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5357 q = 1) (hb : d174735 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d174735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5357, d174735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128197 q = 1) (hb : d174736 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d174736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128197, d174736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128205 q = 1) (hb : d174737 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d174737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, d174737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128206 q = 1) (hb : d174738 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d174738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, d174738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128207 q = 1) (hb : d174739 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d174739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d174739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro39252 (p : Pattern) (ha : d174751 p = 1) (hb : d175345 p = 1) : d175450 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d128212 q = 1) : d128212 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128208 q = 1) (hb : d174740 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d174740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128208, d174740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39251 q ha hb
  have h3 (q : Pattern) (ha : d407 q = 1) (hb : d174746 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d174746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d407, d174746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39246 q ha hb
  have h4 (q : Pattern) (ha : d128209 q = 1) (hb : d174747 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d174747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128209, d174747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128210 q = 1) (hb : d174748 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d174748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128210, d174748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128211 q = 1) (hb : d174749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d174749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128211, d174749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d174750 q = 1) (hb : d175344 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174750, d175344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d174750, d175344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d174751 q = 1) (hb : d175345 q = 1) : d175450 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174751, d175345, d175450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d174751, d175345, d175450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39253 (p : Pattern) (ha : d174757 p = 1) (hb : d175351 p = 1) : d175456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d174675 q = 1) (hb : d175333 q = 1) : d2673 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174675, d175333, d2673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174675, d175333, d2673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39240 q ha hb
  have h2 (q : Pattern) (ha : d174676 q = 1) (hb : d175334 q = 1) : d2674 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174676, d175334, d2674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174676, d175334, d2674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d174677 q = 1) (hb : d175335 q = 1) : d2675 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174677, d175335, d2675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174677, d175335, d2675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d174678 q = 1) (hb : d175336 q = 1) : d2676 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174678, d175336, d2676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174678, d175336, d2676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d174706 q = 1) (hb : d175339 q = 1) : d54299 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174706, d175339, d54299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174706, d175339, d54299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39245 q ha hb
  have h6 (q : Pattern) (ha : d174707 q = 1) (hb : d175340 q = 1) : d54300 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174707, d175340, d54300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174707, d175340, d54300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d174708 q = 1) (hb : d175341 q = 1) : d54301 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174708, d175341, d54301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174708, d175341, d54301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d174709 q = 1) (hb : d175342 q = 1) : d54302 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174709, d175342, d54302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174709, d175342, d54302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d174710 q = 1) (hb : d175343 q = 1) : d54303 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174710, d175343, d54303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d174710, d175343, d54303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d174752 q = 1) (hb : d175346 q = 1) : d175451 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174752, d175346, d175451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174752, d175346, d175451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39252 q ha hb
  have h11 (q : Pattern) (ha : d174753 q = 1) (hb : d175347 q = 1) : d175452 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174753, d175347, d175452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174753, d175347, d175452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d174754 q = 1) (hb : d175348 q = 1) : d175453 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174754, d175348, d175453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174754, d175348, d175453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d174755 q = 1) (hb : d175349 q = 1) : d175454 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174755, d175349, d175454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174755, d175349, d175454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d174756 q = 1) (hb : d175350 q = 1) : d175455 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174756, d175350, d175455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174756, d175350, d175455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d174757 q = 1) (hb : d175351 q = 1) : d175456 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174757, d175351, d175456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d174757, d175351, d175456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39254 (p : Pattern) (ha : d481 p = 1) (hb : d174786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d174682 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d174682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39241 q ha hb
    | true =>
      simp only [d145, d174682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39236 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d174683 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d174683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d174683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d174684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d174684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d174684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d475 q = 1) (hb : d174776 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d174776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d475, d174776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d480 q = 1) (hb : d174785 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d174785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d480, d174785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d481 q = 1) (hb : d174786 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d174786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d481, d174786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39255 (p : Pattern) (ha : d501 p = 1) (hb : d174797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d174787 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d174787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39254 q ha hb
    | true =>
      simp only [d482, d174787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d174788 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d174788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d174788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d174794 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d174794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d174794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d174795 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d174795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d174795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d174796 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d174796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d174796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d174797 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d174797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d174797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39256 (p : Pattern) (ha : d653 p = 1) (hb : d174816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d174811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d174811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39255 q ha hb
    | true =>
      simp only [d639, d174811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d174812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d174812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d174812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d174813 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d174813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d174813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d174814 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d174814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d174814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d174815 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d174815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d174815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d174816 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d174816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d174816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39257 (p : Pattern) (ha : d16036 p = 1) (hb : d174778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d174716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d174716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39248 q ha hb
    | true =>
      simp only [d15967, d174716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39241 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d174717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d174717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d174717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d174718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d174718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d174718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d174682 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d174682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39241 q ha hb
    | true =>
      simp only [d145, d174682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39236 q ha hb
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d174683 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d174683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d174683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d174684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d174684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d174684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15970 q = 1) (hb : d174719 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d174719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d174719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d475 q = 1) (hb : d174776 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d174776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d475, d174776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16035 q = 1) (hb : d174777 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d174777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16035, d174777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16036 q = 1) (hb : d174778 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d174778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16036, d174778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39258 (p : Pattern) (ha : d16051 p = 1) (hb : d174792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d174779 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d174779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39257 q ha hb
    | true =>
      simp only [d16037, d174779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d174780 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d174780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d174780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d174787 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d174787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39254 q ha hb
    | true =>
      simp only [d482, d174787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d174788 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d174788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d174788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d174789 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d174789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d174789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d174790 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d174790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d174790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d174791 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d174791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d174791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d174792 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d174792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d174792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39259 (p : Pattern) (ha : d16077 p = 1) (hb : d174763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d544 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d545 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d546 q = 1) (hb : d174758 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d174758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d546, d174758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9458 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9460 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d16073 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16074 q = 1) (hb : d174759 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d174759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16074, d174759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d16075 q = 1) (hb : d174760 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d174760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16075, d174760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9470 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d12748 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12749 q = 1) (hb : d174761 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d174761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12749, d174761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d9384 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h20 (q : Pattern) (ha : d12493 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12494 q = 1) (hb : d174713 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d174713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12494, d174713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d16076 q = 1) (hb : d174762 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16076, d174762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16076, d174762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d16077 q = 1) (hb : d174763 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16077, d174763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16077, d174763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39260 (p : Pattern) (ha : d16081 p = 1) (hb : d174767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9384 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12493 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12494 q = 1) (hb : d174713 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d174713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12494, d174713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d26 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d27 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28 q = 1) (hb : d174648 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d174648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28, d174648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d12495 q = 1) (hb : d174714 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d174714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12495, d174714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d29 q = 1) (hb : d174649 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d174649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29, d174649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d16081 q = 1) (hb : d174767 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d174767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16081, d174767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39261 (p : Pattern) (ha : d16087 p = 1) (hb : d174773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16078 q = 1) (hb : d174764 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, d174764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39259 q ha hb
    | true =>
      simp only [d16078, d174764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39248 q ha hb
  have h2 (q : Pattern) (ha : d16079 q = 1) (hb : d174765 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16079, d174765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16079, d174765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16080 q = 1) (hb : d174766 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16080, d174766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16080, d174766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d174768 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d174768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39248 q ha hb
    | true =>
      simp only [d16082, d174768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39260 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d174769 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d174769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d174769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d174770 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d174770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d174770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16085 q = 1) (hb : d174771 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16085, d174771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16085, d174771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d174716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d174716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39248 q ha hb
    | true =>
      simp only [d15967, d174716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39241 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d174717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d174717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d174717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d174718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d174718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d174718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145 q = 1) (hb : d174682 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d174682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39241 q ha hb
    | true =>
      simp only [d145, d174682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39236 q ha hb
  have h12 (q : Pattern) (ha : d146 q = 1) (hb : d174683 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d174683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d174683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147 q = 1) (hb : d174684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d174684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d174684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15970 q = 1) (hb : d174719 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d174719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d174719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16086 q = 1) (hb : d174772 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16086, d174772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16086, d174772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16087 q = 1) (hb : d174773 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16087, d174773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16087, d174773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro39262 (p : Pattern) (ha : d16130 p = 1) (hb : d174784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d174774 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d174774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39261 q ha hb
    | true =>
      simp only [d16088, d174774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d174775 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d174775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d174775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d174779 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d174779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39257 q ha hb
    | true =>
      simp only [d16037, d174779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d174780 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d174780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d174780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d174781 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d174781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d174781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d174782 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d174782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d174782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d174783 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d174783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d174783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16130 q = 1) (hb : d174784 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16130, d174784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16130, d174784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39263 (p : Pattern) (ha : d16135 p = 1) (hb : d174803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d174779 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d174779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39257 q ha hb
    | true =>
      simp only [d16037, d174779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d174780 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d174780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d174780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d174800 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d174800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d174800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d174801 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d174801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d174801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d174802 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d174802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d174802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d174803 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d174803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d174803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39264 (p : Pattern) (ha : d128246 p = 1) (hb : d174809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16131 q = 1) (hb : d174793 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d174793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39262 q ha hb
    | true =>
      simp only [d16131, d174793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39258 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d174798 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128235 q = 1) (hb : d174799 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d174799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128235, d174799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16136 q = 1) (hb : d174804 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d174804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39263 q ha hb
    | true =>
      simp only [d16136, d174804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16137 q = 1) (hb : d174805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d174805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16137, d174805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128236 q = 1) (hb : d174806 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d174806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128236, d174806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128244 q = 1) (hb : d174807 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128244, d174807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128244, d174807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128245 q = 1) (hb : d174808 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128245, d174808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128245, d174808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128246 q = 1) (hb : d174809 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d174809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128246, d174809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro39265 (p : Pattern) (ha : d174822 p = 1) (hb : d175353 p = 1) : d175457 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d128251 q = 1) : d128251 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128247 q = 1) (hb : d174810 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d174810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128247, d174810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39264 q ha hb
  have h3 (q : Pattern) (ha : d654 q = 1) (hb : d174817 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d174817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d654, d174817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39256 q ha hb
  have h4 (q : Pattern) (ha : d128248 q = 1) (hb : d174818 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d174818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128248, d174818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128249 q = 1) (hb : d174819 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d174819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128249, d174819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128250 q = 1) (hb : d174820 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d174820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128250, d174820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d174821 q = 1) (hb : d175352 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174821, d175352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d174821, d175352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d174822 q = 1) (hb : d175353 q = 1) : d175457 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174822, d175353, d175457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d174822, d175353, d175457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39266 (p : Pattern) (ha : d174828 p = 1) (hb : d175359 p = 1) : d175463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d174823 q = 1) (hb : d175354 q = 1) : d175458 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174823, d175354, d175458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174823, d175354, d175458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39265 q ha hb
  have h2 (q : Pattern) (ha : d174824 q = 1) (hb : d175355 q = 1) : d175459 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174824, d175355, d175459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174824, d175355, d175459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d174825 q = 1) (hb : d175356 q = 1) : d175460 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174825, d175356, d175460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174825, d175356, d175460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d174826 q = 1) (hb : d175357 q = 1) : d175461 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174826, d175357, d175461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174826, d175357, d175461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d174827 q = 1) (hb : d175358 q = 1) : d175462 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174827, d175358, d175462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174827, d175358, d175462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d174828 q = 1) (hb : d175359 q = 1) : d175463 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174828, d175359, d175463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174828, d175359, d175463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39267 (p : Pattern) (ha : d758 p = 1) (hb : d174849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d321 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322 q = 1) (hb : d174711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d174711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322, d174711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d752 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d753 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d754 q = 1) (hb : d174836 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d174836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d754, d174836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d755 q = 1) (hb : d174848 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d174848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d755, d174848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d757 q = 1) (hb : d174842 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d174842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d757, d174842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d758 q = 1) (hb : d174849 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d174849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d758, d174849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39268 (p : Pattern) (ha : d762 p = 1) (hb : d174853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d752 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d753 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d754 q = 1) (hb : d174836 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d174836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d754, d174836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d757 q = 1) (hb : d174842 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d174842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d757, d174842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d762 q = 1) (hb : d174853 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, d174853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d762, d174853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro39269 (p : Pattern) (ha : d773 p = 1) (hb : d174872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d174854 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d174854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39267 q ha hb
    | true =>
      simp only [d763, d174854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39268 q ha hb
  have h2 (q : Pattern) (ha : d764 q = 1) (hb : d174855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d174855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d174855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d765 q = 1) (hb : d174856 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d174856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d174856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d767 q = 1) (hb : d174862 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d174862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d767, d174862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d772 q = 1) (hb : d174871 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d174871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d772, d174871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d773 q = 1) (hb : d174872 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d174872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d773, d174872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39270 (p : Pattern) (ha : d793 p = 1) (hb : d174883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d174873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d174873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39269 q ha hb
    | true =>
      simp only [d774, d174873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d174874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d174874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d174874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d174880 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d174880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d174880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d174881 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d174881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d174881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d174882 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d174882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d174882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d174883 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d174883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d174883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39271 (p : Pattern) (ha : d959 p = 1) (hb : d174902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d174897 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d174897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39270 q ha hb
    | true =>
      simp only [d945, d174897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d174898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d174898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d174898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d174899 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d174899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d174899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d174900 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d174900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d174900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d174901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d174901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d174901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d174902 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d174902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d174902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39272 (p : Pattern) (ha : d16227 p = 1) (hb : d174838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d544 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d545 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d546 q = 1) (hb : d174758 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d174758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d546, d174758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9458 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9460 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d16073 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16074 q = 1) (hb : d174759 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d174759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16074, d174759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d16075 q = 1) (hb : d174760 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d174760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16075, d174760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9470 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d12748 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12749 q = 1) (hb : d174761 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d174761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12749, d174761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d752 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h20 (q : Pattern) (ha : d753 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d754 q = 1) (hb : d174836 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d174836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d754, d174836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d12750 q = 1) (hb : d174837 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d174837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12750, d174837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d16227 q = 1) (hb : d174838 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16227, d174838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16227, d174838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39273 (p : Pattern) (ha : d16233 p = 1) (hb : d174864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16228 q = 1) (hb : d174850 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d174850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39272 q ha hb
    | true =>
      simp only [d16228, d174850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39267 q ha hb
  have h2 (q : Pattern) (ha : d16229 q = 1) (hb : d174851 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d174851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d174851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16230 q = 1) (hb : d174852 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d174852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d174852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d174854 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d174854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39267 q ha hb
    | true =>
      simp only [d763, d174854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39268 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d174855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d174855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d174855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d174856 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d174856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d174856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16231 q = 1) (hb : d174857 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d174857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16231, d174857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d767 q = 1) (hb : d174862 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d174862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d767, d174862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16232 q = 1) (hb : d174863 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16232, d174863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16232, d174863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16233 q = 1) (hb : d174864 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16233, d174864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16233, d174864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39274 (p : Pattern) (ha : d16248 p = 1) (hb : d174878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d174865 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d174865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39273 q ha hb
    | true =>
      simp only [d16234, d174865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d174866 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d174866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d174866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d174873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d174873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39269 q ha hb
    | true =>
      simp only [d774, d174873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d174874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d174874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d174874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d174875 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d174875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d174875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d174876 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d174876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d174876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d174877 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d174877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d174877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16248 q = 1) (hb : d174878 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16248, d174878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16248, d174878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39275 (p : Pattern) (ha : d16274 p = 1) (hb : d174835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d835 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d836 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d837 q = 1) (hb : d174830 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d174830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d837, d174830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101167 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9587 q = 1) (hb : d101167 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23290 q ha hb
    | true =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9589 q = 1) (hb : d101167 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d16270 q = 1) (hb : d101167 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16271 q = 1) (hb : d174831 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16271, d174831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16271, d174831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d16272 q = 1) (hb : d174832 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16272, d174832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16272, d174832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101177 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9597 q = 1) (hb : d101177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23291 q ha hb
    | true =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9599 q = 1) (hb : d101177 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d14529 q = 1) (hb : d101177 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14530 q = 1) (hb : d174833 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14530, d174833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d14530, d174833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d9470 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h20 (q : Pattern) (ha : d12748 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12749 q = 1) (hb : d174761 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d174761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12749, d174761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d16273 q = 1) (hb : d174834 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16273, d174834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16273, d174834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d16274 q = 1) (hb : d174835 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16274, d174835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16274, d174835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39276 (p : Pattern) (ha : d16278 p = 1) (hb : d174843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9470 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12748 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12749 q = 1) (hb : d174761 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d174761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12749, d174761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d752 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d753 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d754 q = 1) (hb : d174836 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d174836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d754, d174836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d12750 q = 1) (hb : d174837 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d174837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12750, d174837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d757 q = 1) (hb : d174842 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d174842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d757, d174842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d16278 q = 1) (hb : d174843 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16278, d174843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16278, d174843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39277 (p : Pattern) (ha : d16284 p = 1) (hb : d174859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16275 q = 1) (hb : d174839 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, d174839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39275 q ha hb
    | true =>
      simp only [d16275, d174839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39272 q ha hb
  have h2 (q : Pattern) (ha : d16276 q = 1) (hb : d174840 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16276, d174840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16276, d174840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16277 q = 1) (hb : d174841 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16277, d174841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16277, d174841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16279 q = 1) (hb : d174844 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, d174844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39272 q ha hb
    | true =>
      simp only [d16279, d174844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39276 q ha hb
  have h5 (q : Pattern) (ha : d16280 q = 1) (hb : d174845 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16280, d174845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16280, d174845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16281 q = 1) (hb : d174846 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16281, d174846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16281, d174846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16282 q = 1) (hb : d174847 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16282, d174847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16282, d174847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16228 q = 1) (hb : d174850 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d174850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39272 q ha hb
    | true =>
      simp only [d16228, d174850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39267 q ha hb
  have h9 (q : Pattern) (ha : d16229 q = 1) (hb : d174851 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d174851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d174851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16230 q = 1) (hb : d174852 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d174852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d174852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d763 q = 1) (hb : d174854 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d174854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39267 q ha hb
    | true =>
      simp only [d763, d174854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39268 q ha hb
  have h12 (q : Pattern) (ha : d764 q = 1) (hb : d174855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d174855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d174855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d765 q = 1) (hb : d174856 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d174856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d174856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16231 q = 1) (hb : d174857 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d174857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16231, d174857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16283 q = 1) (hb : d174858 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16283, d174858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16283, d174858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16284 q = 1) (hb : d174859 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16284, d174859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16284, d174859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro39278 (p : Pattern) (ha : d16330 p = 1) (hb : d174870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d174860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d174860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39277 q ha hb
    | true =>
      simp only [d16285, d174860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d174861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d174861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d174861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d174865 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d174865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39273 q ha hb
    | true =>
      simp only [d16234, d174865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d174866 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d174866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d174866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d174867 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d174867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d174867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d174868 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d174868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d174868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d174869 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d174869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d174869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16330 q = 1) (hb : d174870 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16330, d174870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16330, d174870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39279 (p : Pattern) (ha : d16335 p = 1) (hb : d174889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d174865 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d174865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39273 q ha hb
    | true =>
      simp only [d16234, d174865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d174866 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d174866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d174866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d174886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d174886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d174886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d174887 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d174887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d174887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d174888 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d174888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d174888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16335 q = 1) (hb : d174889 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16335, d174889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16335, d174889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39280 (p : Pattern) (ha : d128286 p = 1) (hb : d174895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16331 q = 1) (hb : d174879 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d174879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39278 q ha hb
    | true =>
      simp only [d16331, d174879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39274 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d174884 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128275 q = 1) (hb : d174885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d174885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128275, d174885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16336 q = 1) (hb : d174890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d174890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39279 q ha hb
    | true =>
      simp only [d16336, d174890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16337 q = 1) (hb : d174891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d174891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16337, d174891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128276 q = 1) (hb : d174892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d174892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128276, d174892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128284 q = 1) (hb : d174893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128284, d174893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128284, d174893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128285 q = 1) (hb : d174894 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128285, d174894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128285, d174894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128286 q = 1) (hb : d174895 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d174895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128286, d174895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro39281 (p : Pattern) (ha : d174908 p = 1) (hb : d175362 p = 1) : d175465 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d128291 q = 1) : d128291 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128287 q = 1) (hb : d174896 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128287, d174896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128287, d174896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39280 q ha hb
  have h3 (q : Pattern) (ha : d960 q = 1) (hb : d174903 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d174903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d960, d174903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39271 q ha hb
  have h4 (q : Pattern) (ha : d128288 q = 1) (hb : d174904 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128288, d174904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128288, d174904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128289 q = 1) (hb : d174905 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128289, d174905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128289, d174905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128290 q = 1) (hb : d174906 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128290, d174906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128290, d174906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d174907 q = 1) (hb : d175361 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174907, d175361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d174907, d175361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d174908 q = 1) (hb : d175362 q = 1) : d175465 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174908, d175362, d175465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d174908, d175362, d175465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39282 (p : Pattern) (ha : d174914 p = 1) (hb : d175368 p = 1) : d175471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d174909 q = 1) (hb : d175363 q = 1) : d175466 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174909, d175363, d175466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174909, d175363, d175466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39281 q ha hb
  have h2 (q : Pattern) (ha : d174910 q = 1) (hb : d175364 q = 1) : d175467 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174910, d175364, d175467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174910, d175364, d175467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d174911 q = 1) (hb : d175365 q = 1) : d175468 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174911, d175365, d175468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174911, d175365, d175468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d174912 q = 1) (hb : d175366 q = 1) : d175469 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174912, d175366, d175469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174912, d175366, d175469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d174913 q = 1) (hb : d175367 q = 1) : d175470 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174913, d175367, d175470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174913, d175367, d175470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d174914 q = 1) (hb : d175368 q = 1) : d175471 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174914, d175368, d175471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174914, d175368, d175471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39283 (p : Pattern) (ha : d14778 p = 1) (hb : d174971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1122 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1123 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1124 q = 1) (hb : d174942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d174942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1124, d174942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1127 q = 1) (hb : d174970 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d174970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1127, d174970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9846 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d14770 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14771 q = 1) (hb : d174950 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d174950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14771, d174950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d14772 q = 1) (hb : d174951 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d174951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14772, d174951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d14778 q = 1) (hb : d174971 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14778, d174971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14778, d174971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39284 (p : Pattern) (ha : d16443 p = 1) (hb : d174944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1111 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1112 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1113 q = 1) (hb : d174941 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d174941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1113, d174941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1122 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d1123 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1124 q = 1) (hb : d174942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d174942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1124, d174942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1125 q = 1) (hb : d174943 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d174943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1125, d174943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9802 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d14763 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14764 q = 1) (hb : d174927 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d174927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d14764, d174927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d14765 q = 1) (hb : d174935 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d174935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14765, d174935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d16443 q = 1) (hb : d174944 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16443, d174944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16443, d174944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro39285 (p : Pattern) (ha : d16460 p = 1) (hb : d174977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16451 q = 1) (hb : d174972 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d174972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39284 q ha hb
    | true =>
      simp only [d16451, d174972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39283 q ha hb
  have h2 (q : Pattern) (ha : d16452 q = 1) (hb : d174973 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d174973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d174973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16453 q = 1) (hb : d174974 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d174974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d174974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16454 q = 1) (hb : d174975 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d174975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16454, d174975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16459 q = 1) (hb : d174976 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16459, d174976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16459, d174976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16460 q = 1) (hb : d174977 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16460, d174977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16460, d174977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39286 (p : Pattern) (ha : d16480 p = 1) (hb : d174996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d174978 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d174978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39285 q ha hb
    | true =>
      simp only [d16461, d174978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d174979 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d174979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d174979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d174993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d174993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d174993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d174994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d174994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d174994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d174995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d174995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d174995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16480 q = 1) (hb : d174996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16480, d174996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16480, d174996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39287 (p : Pattern) (ha : d16643 p = 1) (hb : d175024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16629 q = 1) (hb : d175019 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d175019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39286 q ha hb
    | true =>
      simp only [d16629, d175019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16630 q = 1) (hb : d175020 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d175020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d175020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16631 q = 1) (hb : d175021 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d175021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16631, d175021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16632 q = 1) (hb : d175022 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d175022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d175022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16633 q = 1) (hb : d175023 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d175023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d175023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16643 q = 1) (hb : d175024 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16643, d175024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16643, d175024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39288 (p : Pattern) (ha : d14773 p = 1) (hb : d174952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5018 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7947 q ha hb
    | true =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5019 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5020 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5021 q = 1) (hb : d174948 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5021, d174948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5021, d174948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5022 q = 1) (hb : d174949 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, d174949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5022, d174949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9846 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d14770 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14771 q = 1) (hb : d174950 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d174950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14771, d174950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d14772 q = 1) (hb : d174951 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d174951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14772, d174951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d14773 q = 1) (hb : d174952 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14773, d174952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14773, d174952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39289 (p : Pattern) (ha : d16442 p = 1) (hb : d174929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1101 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1102 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1103 q = 1) (hb : d174924 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d174924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1103, d174924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101310 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9789 q = 1) (hb : d101310 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23315 q ha hb
    | true =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9791 q = 1) (hb : d101310 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d16438 q = 1) (hb : d101310 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16439 q = 1) (hb : d174925 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16439, d174925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16439, d174925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d16440 q = 1) (hb : d174926 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16440, d174926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16440, d174926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9778 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9780 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d14758 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14759 q = 1) (hb : d174921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d174921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d14759, d174921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d9802 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h20 (q : Pattern) (ha : d14763 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14764 q = 1) (hb : d174927 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d174927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14764, d174927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d16441 q = 1) (hb : d174928 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16441, d174928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16441, d174928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d16442 q = 1) (hb : d174929 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16442, d174929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16442, d174929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39290 (p : Pattern) (ha : d16511 p = 1) (hb : d174923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1211 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1212 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1213 q = 1) (hb : d174917 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d174917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1213, d174917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101274 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9753 q = 1) (hb : d101274 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23310 q ha hb
    | true =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9755 q = 1) (hb : d101274 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d16507 q = 1) (hb : d101274 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16508 q = 1) (hb : d174918 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16508, d174918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16508, d174918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d16509 q = 1) (hb : d174919 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16509, d174919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16509, d174919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101284 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9763 q = 1) (hb : d101284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23311 q ha hb
    | true =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9765 q = 1) (hb : d101284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d14836 q = 1) (hb : d101284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14837 q = 1) (hb : d174920 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14837, d174920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d14837, d174920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d9778 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d9780 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h20 (q : Pattern) (ha : d14758 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14759 q = 1) (hb : d174921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d174921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14759, d174921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d16510 q = 1) (hb : d174922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16510, d174922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16510, d174922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d16511 q = 1) (hb : d174923 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16511, d174923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16511, d174923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39291 (p : Pattern) (ha : d16516 p = 1) (hb : d174936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9814 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23317 q ha hb
    | true =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9816 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13022 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13023 q = 1) (hb : d174933 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13023, d174933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13023, d174933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9802 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d14763 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14764 q = 1) (hb : d174927 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d174927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14764, d174927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d16515 q = 1) (hb : d174934 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16515, d174934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16515, d174934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14765 q = 1) (hb : d174935 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d174935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14765, d174935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d16516 q = 1) (hb : d174936 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16516, d174936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16516, d174936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39292 (p : Pattern) (ha : d16522 p = 1) (hb : d174958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16512 q = 1) (hb : d174930 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16512, d174930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39290 q ha hb
    | true =>
      simp only [d16512, d174930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39289 q ha hb
  have h2 (q : Pattern) (ha : d16513 q = 1) (hb : d174931 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16513, d174931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16513, d174931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16514 q = 1) (hb : d174932 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16514, d174932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16514, d174932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16517 q = 1) (hb : d174937 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16517, d174937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39289 q ha hb
    | true =>
      simp only [d16517, d174937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39291 q ha hb
  have h5 (q : Pattern) (ha : d16518 q = 1) (hb : d174938 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16518, d174938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16518, d174938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16519 q = 1) (hb : d174939 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16519, d174939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16519, d174939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16520 q = 1) (hb : d174940 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16520, d174940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16520, d174940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16444 q = 1) (hb : d174945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d174945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39289 q ha hb
    | true =>
      simp only [d16444, d174945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39284 q ha hb
  have h9 (q : Pattern) (ha : d16445 q = 1) (hb : d174946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d174946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d174946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16446 q = 1) (hb : d174947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d174947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d174947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16447 q = 1) (hb : d174953 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d174953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39284 q ha hb
    | true =>
      simp only [d16447, d174953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39288 q ha hb
  have h12 (q : Pattern) (ha : d16448 q = 1) (hb : d174954 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d174954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d174954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16449 q = 1) (hb : d174955 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d174955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d174955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16450 q = 1) (hb : d174956 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d174956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16450, d174956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16521 q = 1) (hb : d174957 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16521, d174957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16521, d174957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16522 q = 1) (hb : d174958 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16522, d174958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16522, d174958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro39293 (p : Pattern) (ha : d16527 p = 1) (hb : d174963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d174945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d174945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39289 q ha hb
    | true =>
      simp only [d16444, d174945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39284 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d174946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d174946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d174946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d174947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d174947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d174947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d174953 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d174953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39284 q ha hb
    | true =>
      simp only [d16447, d174953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39288 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d174954 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d174954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d174954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d174955 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d174955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d174955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d174956 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d174956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d174956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16525 q = 1) (hb : d174961 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16525, d174961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16525, d174961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16526 q = 1) (hb : d174962 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16526, d174962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16526, d174962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16527 q = 1) (hb : d174963 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16527, d174963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16527, d174963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39294 (p : Pattern) (ha : d16603 p = 1) (hb : d174969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d174959 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d174959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39292 q ha hb
    | true =>
      simp only [d16523, d174959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d174960 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d174960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d174960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d174964 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d174964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39293 q ha hb
    | true =>
      simp only [d16528, d174964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d174965 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d174965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d174965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d174966 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d174966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d174966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d174967 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d174967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d174967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d174968 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d174968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d174968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16603 q = 1) (hb : d174969 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16603, d174969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16603, d174969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39295 (p : Pattern) (ha : d16604 p = 1) (hb : d174983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d174964 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d174964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39293 q ha hb
    | true =>
      simp only [d16528, d174964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d174965 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d174965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d174965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d174978 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d174978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39285 q ha hb
    | true =>
      simp only [d16461, d174978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d174979 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d174979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d174979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d174980 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d174980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d174980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d174981 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d174981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d174981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d174982 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d174982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d174982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16604 q = 1) (hb : d174983 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16604, d174983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16604, d174983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39296 (p : Pattern) (ha : d12961 p = 1) (hb : d174999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1122 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1123 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1124 q = 1) (hb : d174942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d174942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1124, d174942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1127 q = 1) (hb : d174970 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d174970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1127, d174970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d12961 q = 1) (hb : d174999 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12961, d174999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12961, d174999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro39297 (p : Pattern) (ha : d16579 p = 1) (hb : d175005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d174945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d174945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39289 q ha hb
    | true =>
      simp only [d16444, d174945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39284 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d174946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d174946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d174946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d174947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d174947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d174947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d174953 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d174953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39284 q ha hb
    | true =>
      simp only [d16447, d174953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39288 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d174954 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d174954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d174954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d174955 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d174955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d174955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d174956 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d174956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d174956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16574 q = 1) (hb : d175000 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16574, d175000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39284 q ha hb
    | true =>
      simp only [d16574, d175000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39296 q ha hb
  have h9 (q : Pattern) (ha : d16575 q = 1) (hb : d175001 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16575, d175001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16575, d175001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16576 q = 1) (hb : d175002 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16576, d175002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16576, d175002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16577 q = 1) (hb : d175003 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16577, d175003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16577, d175003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16578 q = 1) (hb : d175004 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16578, d175004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16578, d175004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16579 q = 1) (hb : d175005 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16579, d175005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16579, d175005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39298 (p : Pattern) (ha : d16610 p = 1) (hb : d175011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d175006 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d175006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39297 q ha hb
    | true =>
      simp only [d16580, d175006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d175007 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d175007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d175007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d175008 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d175008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d175008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d175009 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d175009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d175009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d175010 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d175010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d175010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16610 q = 1) (hb : d175011 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16610, d175011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16610, d175011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39299 (p : Pattern) (ha : d128327 p = 1) (hb : d175017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16605 q = 1) (hb : d174984 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d174984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39294 q ha hb
    | true =>
      simp only [d16605, d174984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39295 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d174997 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128316 q = 1) (hb : d174998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d174998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128316, d174998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16611 q = 1) (hb : d175012 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d175012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39298 q ha hb
    | true =>
      simp only [d16611, d175012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16612 q = 1) (hb : d175013 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d175013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16612, d175013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128317 q = 1) (hb : d175014 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d175014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128317, d175014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128325 q = 1) (hb : d175015 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128325, d175015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128325, d175015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128326 q = 1) (hb : d175016 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128326, d175016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128326, d175016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128327 q = 1) (hb : d175017 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128327, d175017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128327, d175017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro39300 (p : Pattern) (ha : d175030 p = 1) (hb : d175372 p = 1) : d175474 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d128332 q = 1) : d128332 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128328 q = 1) (hb : d175018 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128328, d175018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128328, d175018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39299 q ha hb
  have h3 (q : Pattern) (ha : d16644 q = 1) (hb : d175025 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16644, d175025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16644, d175025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39287 q ha hb
  have h4 (q : Pattern) (ha : d128329 q = 1) (hb : d175026 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128329, d175026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128329, d175026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128330 q = 1) (hb : d175027 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128330, d175027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128330, d175027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128331 q = 1) (hb : d175028 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128331, d175028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128331, d175028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175029 q = 1) (hb : d175371 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175029, d175371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d175029, d175371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d175030 q = 1) (hb : d175372 q = 1) : d175474 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175030, d175372, d175474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175030, d175372, d175474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39301 (p : Pattern) (ha : d175036 p = 1) (hb : d175378 p = 1) : d175480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175031 q = 1) (hb : d175373 q = 1) : d175475 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175031, d175373, d175475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175031, d175373, d175475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39300 q ha hb
  have h2 (q : Pattern) (ha : d175032 q = 1) (hb : d175374 q = 1) : d175476 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175032, d175374, d175476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175032, d175374, d175476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175033 q = 1) (hb : d175375 q = 1) : d175477 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175033, d175375, d175477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175033, d175375, d175477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175034 q = 1) (hb : d175376 q = 1) : d175478 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175034, d175376, d175478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175034, d175376, d175478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d175035 q = 1) (hb : d175377 q = 1) : d175479 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175035, d175377, d175479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175035, d175377, d175479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175036 q = 1) (hb : d175378 q = 1) : d175480 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175036, d175378, d175480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175036, d175378, d175480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39302 (p : Pattern) (ha : d15171 p = 1) (hb : d175095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1583 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1584 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1585 q = 1) (hb : d175093 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d175093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1585, d175093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1588 q = 1) (hb : d175094 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d175094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1588, d175094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10137 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d15163 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15164 q = 1) (hb : d175073 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d175073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15164, d175073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d15165 q = 1) (hb : d175074 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d175074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15165, d175074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d15171 q = 1) (hb : d175095 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15171, d175095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15171, d175095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39303 (p : Pattern) (ha : d16795 p = 1) (hb : d175067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1571 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1572 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1573 q = 1) (hb : d175064 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d175064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1573, d175064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101542 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10115 q = 1) (hb : d101542 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23331 q ha hb
    | true =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10117 q = 1) (hb : d101542 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d16792 q = 1) (hb : d101542 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16793 q = 1) (hb : d175065 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16793, d175065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16793, d175065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d16794 q = 1) (hb : d175066 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16794, d175066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16794, d175066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10087 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d15156 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15157 q = 1) (hb : d175050 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d175050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15157, d175050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d15158 q = 1) (hb : d175058 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d175058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15158, d175058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d16795 q = 1) (hb : d175067 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16795, d175067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16795, d175067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro39304 (p : Pattern) (ha : d16812 p = 1) (hb : d175101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16803 q = 1) (hb : d175096 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d175096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39303 q ha hb
    | true =>
      simp only [d16803, d175096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39302 q ha hb
  have h2 (q : Pattern) (ha : d16804 q = 1) (hb : d175097 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d175097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d175097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16805 q = 1) (hb : d175098 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d175098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d175098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16806 q = 1) (hb : d175099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d175099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16806, d175099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16811 q = 1) (hb : d175100 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16811, d175100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16811, d175100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16812 q = 1) (hb : d175101 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16812, d175101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16812, d175101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39305 (p : Pattern) (ha : d16832 p = 1) (hb : d175120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d175102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d175102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39304 q ha hb
    | true =>
      simp only [d16813, d175102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d175103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d175103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d175103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d175117 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d175117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d175117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d175118 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d175118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d175118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d175119 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d175119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d175119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16832 q = 1) (hb : d175120 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16832, d175120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16832, d175120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39306 (p : Pattern) (ha : d16998 p = 1) (hb : d175148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16984 q = 1) (hb : d175143 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d175143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39305 q ha hb
    | true =>
      simp only [d16984, d175143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16985 q = 1) (hb : d175144 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d175144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d175144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16986 q = 1) (hb : d175145 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d175145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16986, d175145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16987 q = 1) (hb : d175146 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d175146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d175146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16988 q = 1) (hb : d175147 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d175147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d175147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16998 q = 1) (hb : d175148 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16998, d175148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16998, d175148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39307 (p : Pattern) (ha : d15166 p = 1) (hb : d175075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5134 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
    | true =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5135 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5136 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5137 q = 1) (hb : d175071 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5137, d175071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5137, d175071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5138 q = 1) (hb : d175072 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d175072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5138, d175072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10137 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d15163 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15164 q = 1) (hb : d175073 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d175073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15164, d175073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d15165 q = 1) (hb : d175074 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d175074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15165, d175074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d15166 q = 1) (hb : d175075 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15166, d175075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15166, d175075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39308 (p : Pattern) (ha : d16791 p = 1) (hb : d175052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1556 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1557 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1558 q = 1) (hb : d175047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d175047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1558, d175047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101501 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10074 q = 1) (hb : d101501 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23343 q ha hb
    | true =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10076 q = 1) (hb : d101501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d16787 q = 1) (hb : d101501 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16788 q = 1) (hb : d175048 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16788, d175048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16788, d175048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d16789 q = 1) (hb : d175049 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16789, d175049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16789, d175049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10063 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10065 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d15151 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15152 q = 1) (hb : d175044 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d175044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15152, d175044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d10087 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h20 (q : Pattern) (ha : d15156 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15157 q = 1) (hb : d175050 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d175050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15157, d175050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d16790 q = 1) (hb : d175051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16790, d175051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16790, d175051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d16791 q = 1) (hb : d175052 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16791, d175052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16791, d175052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39309 (p : Pattern) (ha : d16863 p = 1) (hb : d175046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1666 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1667 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1668 q = 1) (hb : d175040 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, d175040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1668, d175040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10036 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10038 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d16859 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16860 q = 1) (hb : d175041 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d175041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16860, d175041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d16861 q = 1) (hb : d175042 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16861, d175042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16861, d175042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10046 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10048 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d15229 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15230 q = 1) (hb : d175043 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15230, d175043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15230, d175043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d10063 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d10065 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h20 (q : Pattern) (ha : d15151 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15152 q = 1) (hb : d175044 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d175044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15152, d175044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d16862 q = 1) (hb : d175045 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16862, d175045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16862, d175045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d16863 q = 1) (hb : d175046 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16863, d175046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16863, d175046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39310 (p : Pattern) (ha : d16868 p = 1) (hb : d175059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10099 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
    | true =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10101 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13348 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13349 q = 1) (hb : d175056 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13349, d175056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13349, d175056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10087 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d15156 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15157 q = 1) (hb : d175050 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d175050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15157, d175050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d16867 q = 1) (hb : d175057 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16867, d175057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16867, d175057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15158 q = 1) (hb : d175058 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d175058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15158, d175058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d16868 q = 1) (hb : d175059 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16868, d175059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16868, d175059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39311 (p : Pattern) (ha : d16874 p = 1) (hb : d175081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16864 q = 1) (hb : d175053 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16864, d175053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39309 q ha hb
    | true =>
      simp only [d16864, d175053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39308 q ha hb
  have h2 (q : Pattern) (ha : d16865 q = 1) (hb : d175054 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16865, d175054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16865, d175054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16866 q = 1) (hb : d175055 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16866, d175055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16866, d175055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16869 q = 1) (hb : d175060 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16869, d175060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39308 q ha hb
    | true =>
      simp only [d16869, d175060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39310 q ha hb
  have h5 (q : Pattern) (ha : d16870 q = 1) (hb : d175061 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16870, d175061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16870, d175061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16871 q = 1) (hb : d175062 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16871, d175062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16871, d175062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16872 q = 1) (hb : d175063 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16872, d175063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16872, d175063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16796 q = 1) (hb : d175068 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d175068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39308 q ha hb
    | true =>
      simp only [d16796, d175068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39303 q ha hb
  have h9 (q : Pattern) (ha : d16797 q = 1) (hb : d175069 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d175069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d175069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16798 q = 1) (hb : d175070 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d175070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d175070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16799 q = 1) (hb : d175076 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d175076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39303 q ha hb
    | true =>
      simp only [d16799, d175076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39307 q ha hb
  have h12 (q : Pattern) (ha : d16800 q = 1) (hb : d175077 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d175077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d175077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16801 q = 1) (hb : d175078 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d175078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d175078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16802 q = 1) (hb : d175079 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d175079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16802, d175079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16873 q = 1) (hb : d175080 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16873, d175080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16873, d175080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16874 q = 1) (hb : d175081 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16874, d175081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16874, d175081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro39312 (p : Pattern) (ha : d16879 p = 1) (hb : d175086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d175068 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d175068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39308 q ha hb
    | true =>
      simp only [d16796, d175068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39303 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d175069 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d175069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d175069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d175070 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d175070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d175070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d175076 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d175076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39303 q ha hb
    | true =>
      simp only [d16799, d175076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39307 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d175077 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d175077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d175077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d175078 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d175078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d175078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d175079 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d175079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d175079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16877 q = 1) (hb : d175084 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16877, d175084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16877, d175084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16878 q = 1) (hb : d175085 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16878, d175085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16878, d175085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16879 q = 1) (hb : d175086 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16879, d175086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16879, d175086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39313 (p : Pattern) (ha : d16958 p = 1) (hb : d175092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16875 q = 1) (hb : d175082 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16875, d175082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39311 q ha hb
    | true =>
      simp only [d16875, d175082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16876 q = 1) (hb : d175083 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16876, d175083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16876, d175083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16880 q = 1) (hb : d175087 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d175087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39312 q ha hb
    | true =>
      simp only [d16880, d175087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16881 q = 1) (hb : d175088 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d175088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d175088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16882 q = 1) (hb : d175089 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16882, d175089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16882, d175089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16883 q = 1) (hb : d175090 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16883, d175090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16883, d175090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16884 q = 1) (hb : d175091 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16884, d175091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16884, d175091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16958 q = 1) (hb : d175092 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16958, d175092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16958, d175092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39314 (p : Pattern) (ha : d16959 p = 1) (hb : d175107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16880 q = 1) (hb : d175087 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d175087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39312 q ha hb
    | true =>
      simp only [d16880, d175087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16881 q = 1) (hb : d175088 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d175088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d175088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d175102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d175102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39304 q ha hb
    | true =>
      simp only [d16813, d175102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d175103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d175103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d175103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16886 q = 1) (hb : d175104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16886, d175104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16886, d175104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16887 q = 1) (hb : d175105 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16887, d175105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16887, d175105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16888 q = 1) (hb : d175106 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16888, d175106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16888, d175106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16959 q = 1) (hb : d175107 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16959, d175107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16959, d175107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39315 (p : Pattern) (ha : d13287 p = 1) (hb : d175123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1583 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1584 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1585 q = 1) (hb : d175093 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d175093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1585, d175093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1588 q = 1) (hb : d175094 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d175094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1588, d175094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d13287 q = 1) (hb : d175123 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, d175123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13287, d175123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro39316 (p : Pattern) (ha : d16934 p = 1) (hb : d175129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d175068 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d175068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39308 q ha hb
    | true =>
      simp only [d16796, d175068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39303 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d175069 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d175069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d175069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d175070 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d175070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d175070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d175076 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d175076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39303 q ha hb
    | true =>
      simp only [d16799, d175076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39307 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d175077 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d175077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d175077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d175078 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d175078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d175078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d175079 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d175079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d175079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16929 q = 1) (hb : d175124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16929, d175124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39303 q ha hb
    | true =>
      simp only [d16929, d175124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39315 q ha hb
  have h9 (q : Pattern) (ha : d16930 q = 1) (hb : d175125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16930, d175125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16930, d175125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16931 q = 1) (hb : d175126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16931, d175126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16931, d175126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16932 q = 1) (hb : d175127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16932, d175127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16932, d175127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16933 q = 1) (hb : d175128 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16933, d175128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16933, d175128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16934 q = 1) (hb : d175129 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16934, d175129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16934, d175129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39317 (p : Pattern) (ha : d16965 p = 1) (hb : d175135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16935 q = 1) (hb : d175130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16935, d175130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39316 q ha hb
    | true =>
      simp only [d16935, d175130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16936 q = 1) (hb : d175131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16936, d175131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16936, d175131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16937 q = 1) (hb : d175132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16937, d175132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16937, d175132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16938 q = 1) (hb : d175133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16938, d175133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16938, d175133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16939 q = 1) (hb : d175134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16939, d175134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16939, d175134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16965 q = 1) (hb : d175135 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16965, d175135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16965, d175135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39318 (p : Pattern) (ha : d128369 p = 1) (hb : d175141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16960 q = 1) (hb : d175108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16960, d175108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39313 q ha hb
    | true =>
      simp only [d16960, d175108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39314 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d175121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128358 q = 1) (hb : d175122 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d175122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128358, d175122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16966 q = 1) (hb : d175136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16966, d175136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39317 q ha hb
    | true =>
      simp only [d16966, d175136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16967 q = 1) (hb : d175137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16967, d175137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16967, d175137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128359 q = 1) (hb : d175138 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d175138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128359, d175138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128367 q = 1) (hb : d175139 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128367, d175139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128367, d175139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128368 q = 1) (hb : d175140 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128368, d175140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128368, d175140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128369 q = 1) (hb : d175141 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128369, d175141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128369, d175141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro39319 (p : Pattern) (ha : d175154 p = 1) (hb : d175383 p = 1) : d175484 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d128374 q = 1) : d128374 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128370 q = 1) (hb : d175142 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128370, d175142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128370, d175142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39318 q ha hb
  have h3 (q : Pattern) (ha : d16999 q = 1) (hb : d175149 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16999, d175149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16999, d175149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39306 q ha hb
  have h4 (q : Pattern) (ha : d128371 q = 1) (hb : d175150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128371, d175150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128371, d175150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128372 q = 1) (hb : d175151 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128372, d175151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128372, d175151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128373 q = 1) (hb : d175152 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128373, d175152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128373, d175152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175153 q = 1) (hb : d175382 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175153, d175382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d175153, d175382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d175154 q = 1) (hb : d175383 q = 1) : d175484 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175154, d175383, d175484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175154, d175383, d175484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39320 (p : Pattern) (ha : d175160 p = 1) (hb : d175389 p = 1) : d175490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175155 q = 1) (hb : d175384 q = 1) : d175485 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175155, d175384, d175485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175155, d175384, d175485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39319 q ha hb
  have h2 (q : Pattern) (ha : d175156 q = 1) (hb : d175385 q = 1) : d175486 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175156, d175385, d175486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175156, d175385, d175486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175157 q = 1) (hb : d175386 q = 1) : d175487 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175157, d175386, d175487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175157, d175386, d175487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175158 q = 1) (hb : d175387 q = 1) : d175488 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175158, d175387, d175488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175158, d175387, d175488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d175159 q = 1) (hb : d175388 q = 1) : d175489 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175159, d175388, d175489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175159, d175388, d175489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175160 q = 1) (hb : d175389 q = 1) : d175490 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175160, d175389, d175490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175160, d175389, d175490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39321 (p : Pattern) (ha : d15563 p = 1) (hb : d175217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2066 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2067 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2068 q = 1) (hb : d175215 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d175215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2068, d175215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2071 q = 1) (hb : d175216 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d175216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2071, d175216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10414 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d15555 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15556 q = 1) (hb : d175195 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d175195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15556, d175195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d15557 q = 1) (hb : d175196 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d175196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15557, d175196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d15563 q = 1) (hb : d175217 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15563, d175217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15563, d175217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39322 (p : Pattern) (ha : d17161 p = 1) (hb : d175189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2054 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2055 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2056 q = 1) (hb : d175186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d175186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2056, d175186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101712 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10391 q = 1) (hb : d101712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23359 q ha hb
    | true =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10393 q = 1) (hb : d101712 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d17158 q = 1) (hb : d101712 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17159 q = 1) (hb : d175187 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17159, d175187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17159, d175187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d17160 q = 1) (hb : d175188 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17160, d175188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17160, d175188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10373 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d15548 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15549 q = 1) (hb : d175174 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d175174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15549, d175174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d15550 q = 1) (hb : d175180 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, d175180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15550, d175180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d17161 q = 1) (hb : d175189 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17161, d175189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17161, d175189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro39323 (p : Pattern) (ha : d17178 p = 1) (hb : d175223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17169 q = 1) (hb : d175218 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d175218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39322 q ha hb
    | true =>
      simp only [d17169, d175218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39321 q ha hb
  have h2 (q : Pattern) (ha : d17170 q = 1) (hb : d175219 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d175219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d175219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17171 q = 1) (hb : d175220 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d175220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d175220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17172 q = 1) (hb : d175221 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d175221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17172, d175221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17177 q = 1) (hb : d175222 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17177, d175222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17177, d175222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17178 q = 1) (hb : d175223 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17178, d175223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17178, d175223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39324 (p : Pattern) (ha : d17198 p = 1) (hb : d175242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d175224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d175224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39323 q ha hb
    | true =>
      simp only [d17179, d175224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d175225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d175225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d175225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d175239 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d175239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d175239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d175240 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d175240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d175240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17187 q = 1) (hb : d175241 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17187, d175241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17187, d175241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17198 q = 1) (hb : d175242 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17198, d175242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17198, d175242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39325 (p : Pattern) (ha : d17363 p = 1) (hb : d175270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17349 q = 1) (hb : d175265 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17349, d175265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39324 q ha hb
    | true =>
      simp only [d17349, d175265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17350 q = 1) (hb : d175266 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17350, d175266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17350, d175266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17351 q = 1) (hb : d175267 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17351, d175267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17351, d175267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17352 q = 1) (hb : d175268 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17352, d175268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17352, d175268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17353 q = 1) (hb : d175269 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17353, d175269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17353, d175269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17363 q = 1) (hb : d175270 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17363, d175270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17363, d175270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39326 (p : Pattern) (ha : d15558 p = 1) (hb : d175197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5247 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
    | true =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5248 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5249 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5250 q = 1) (hb : d175193 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5250, d175193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5250, d175193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5251 q = 1) (hb : d175194 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, d175194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5251, d175194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10414 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d15555 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15556 q = 1) (hb : d175195 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d175195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15556, d175195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d15557 q = 1) (hb : d175196 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d175196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15557, d175196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d15558 q = 1) (hb : d175197 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15558, d175197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15558, d175197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39327 (p : Pattern) (ha : d17157 p = 1) (hb : d175176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2036 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2037 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2038 q = 1) (hb : d175171 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d175171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2038, d175171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10366 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d17153 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17154 q = 1) (hb : d175172 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d175172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17154, d175172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d17155 q = 1) (hb : d175173 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17155, d175173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17155, d175173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10355 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d13675 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13676 q = 1) (hb : d175168 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d175168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13676, d175168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d10373 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h20 (q : Pattern) (ha : d15548 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15549 q = 1) (hb : d175174 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d175174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15549, d175174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d17156 q = 1) (hb : d175175 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, d175175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17156, d175175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d17157 q = 1) (hb : d175176 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17157, d175176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17157, d175176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39328 (p : Pattern) (ha : d17229 p = 1) (hb : d175170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2145 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2146 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2147 q = 1) (hb : d175165 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, d175165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2147, d175165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10345 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d17225 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17226 q = 1) (hb : d175166 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d175166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17226, d175166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d17227 q = 1) (hb : d175167 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17227, d175167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17227, d175167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10355 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d13675 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13676 q = 1) (hb : d175168 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d175168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13676, d175168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d17228 q = 1) (hb : d175169 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17228, d175169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17228, d175169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d17229 q = 1) (hb : d175170 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17229, d175170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17229, d175170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro39329 (p : Pattern) (ha : d17233 p = 1) (hb : d175181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10355 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13675 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13676 q = 1) (hb : d175168 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d175168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13676, d175168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10373 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d15548 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15549 q = 1) (hb : d175174 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d175174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15549, d175174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d17156 q = 1) (hb : d175175 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, d175175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17156, d175175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15550 q = 1) (hb : d175180 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, d175180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15550, d175180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d17233 q = 1) (hb : d175181 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17233, d175181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17233, d175181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39330 (p : Pattern) (ha : d17239 p = 1) (hb : d175203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17230 q = 1) (hb : d175177 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17230, d175177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39328 q ha hb
    | true =>
      simp only [d17230, d175177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39327 q ha hb
  have h2 (q : Pattern) (ha : d17231 q = 1) (hb : d175178 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17231, d175178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17231, d175178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17232 q = 1) (hb : d175179 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17232, d175179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17232, d175179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17234 q = 1) (hb : d175182 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17234, d175182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39327 q ha hb
    | true =>
      simp only [d17234, d175182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39329 q ha hb
  have h5 (q : Pattern) (ha : d17235 q = 1) (hb : d175183 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17235, d175183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17235, d175183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17236 q = 1) (hb : d175184 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17236, d175184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17236, d175184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17237 q = 1) (hb : d175185 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17237, d175185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17237, d175185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17162 q = 1) (hb : d175190 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d175190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39327 q ha hb
    | true =>
      simp only [d17162, d175190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39322 q ha hb
  have h9 (q : Pattern) (ha : d17163 q = 1) (hb : d175191 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d175191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d175191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17164 q = 1) (hb : d175192 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d175192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d175192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17165 q = 1) (hb : d175198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d175198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39322 q ha hb
    | true =>
      simp only [d17165, d175198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39326 q ha hb
  have h12 (q : Pattern) (ha : d17166 q = 1) (hb : d175199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d175199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d175199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17167 q = 1) (hb : d175200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d175200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d175200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17168 q = 1) (hb : d175201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d175201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17168, d175201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17238 q = 1) (hb : d175202 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17238, d175202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17238, d175202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17239 q = 1) (hb : d175203 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17239, d175203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17239, d175203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro39331 (p : Pattern) (ha : d17244 p = 1) (hb : d175208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d175190 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d175190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39327 q ha hb
    | true =>
      simp only [d17162, d175190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39322 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d175191 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d175191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d175191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d175192 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d175192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d175192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d175198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d175198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39322 q ha hb
    | true =>
      simp only [d17165, d175198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39326 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d175199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d175199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d175199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d175200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d175200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d175200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d175201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d175201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d175201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17242 q = 1) (hb : d175206 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17242, d175206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17242, d175206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17243 q = 1) (hb : d175207 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17243, d175207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17243, d175207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17244 q = 1) (hb : d175208 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17244, d175208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17244, d175208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39332 (p : Pattern) (ha : d17323 p = 1) (hb : d175214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17240 q = 1) (hb : d175204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17240, d175204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39330 q ha hb
    | true =>
      simp only [d17240, d175204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17241 q = 1) (hb : d175205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17241, d175205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17241, d175205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17245 q = 1) (hb : d175209 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d175209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39331 q ha hb
    | true =>
      simp only [d17245, d175209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17246 q = 1) (hb : d175210 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d175210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d175210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17247 q = 1) (hb : d175211 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17247, d175211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17247, d175211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17248 q = 1) (hb : d175212 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17248, d175212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17248, d175212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17249 q = 1) (hb : d175213 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17249, d175213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17249, d175213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17323 q = 1) (hb : d175214 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17323, d175214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17323, d175214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39333 (p : Pattern) (ha : d17324 p = 1) (hb : d175229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17245 q = 1) (hb : d175209 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d175209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39331 q ha hb
    | true =>
      simp only [d17245, d175209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17246 q = 1) (hb : d175210 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d175210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d175210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d175224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d175224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39323 q ha hb
    | true =>
      simp only [d17179, d175224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d175225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d175225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d175225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17251 q = 1) (hb : d175226 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17251, d175226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17251, d175226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17252 q = 1) (hb : d175227 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17252, d175227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17252, d175227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17253 q = 1) (hb : d175228 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17253, d175228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17253, d175228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17324 q = 1) (hb : d175229 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17324, d175229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17324, d175229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39334 (p : Pattern) (ha : d13614 p = 1) (hb : d175245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2066 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2067 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2068 q = 1) (hb : d175215 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d175215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2068, d175215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2071 q = 1) (hb : d175216 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d175216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2071, d175216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d13614 q = 1) (hb : d175245 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13614, d175245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13614, d175245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro39335 (p : Pattern) (ha : d17299 p = 1) (hb : d175251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d175190 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d175190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39327 q ha hb
    | true =>
      simp only [d17162, d175190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39322 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d175191 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d175191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d175191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d175192 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d175192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d175192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d175198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d175198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39322 q ha hb
    | true =>
      simp only [d17165, d175198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39326 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d175199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d175199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d175199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d175200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d175200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d175200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d175201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d175201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d175201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17294 q = 1) (hb : d175246 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17294, d175246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39322 q ha hb
    | true =>
      simp only [d17294, d175246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39334 q ha hb
  have h9 (q : Pattern) (ha : d17295 q = 1) (hb : d175247 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17295, d175247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17295, d175247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17296 q = 1) (hb : d175248 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17296, d175248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17296, d175248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17297 q = 1) (hb : d175249 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17297, d175249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17297, d175249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17298 q = 1) (hb : d175250 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17298, d175250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17298, d175250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17299 q = 1) (hb : d175251 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17299, d175251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17299, d175251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39336 (p : Pattern) (ha : d17330 p = 1) (hb : d175257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17300 q = 1) (hb : d175252 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17300, d175252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39335 q ha hb
    | true =>
      simp only [d17300, d175252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17301 q = 1) (hb : d175253 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17301, d175253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17301, d175253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17302 q = 1) (hb : d175254 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17302, d175254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17302, d175254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17303 q = 1) (hb : d175255 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17303, d175255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17303, d175255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17304 q = 1) (hb : d175256 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17304, d175256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17304, d175256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17330 q = 1) (hb : d175257 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17330, d175257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17330, d175257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39337 (p : Pattern) (ha : d128412 p = 1) (hb : d175263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17325 q = 1) (hb : d175230 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17325, d175230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39332 q ha hb
    | true =>
      simp only [d17325, d175230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39333 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d175243 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128401 q = 1) (hb : d175244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d175244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128401, d175244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17331 q = 1) (hb : d175258 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17331, d175258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39336 q ha hb
    | true =>
      simp only [d17331, d175258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17332 q = 1) (hb : d175259 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17332, d175259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17332, d175259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128402 q = 1) (hb : d175260 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d175260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128402, d175260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128410 q = 1) (hb : d175261 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128410, d175261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128410, d175261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128411 q = 1) (hb : d175262 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128411, d175262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128411, d175262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128412 q = 1) (hb : d175263 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128412, d175263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128412, d175263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro39338 (p : Pattern) (ha : d175276 p = 1) (hb : d175395 p = 1) : d175495 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d128417 q = 1) : d128417 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128413 q = 1) (hb : d175264 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128413, d175264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128413, d175264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39337 q ha hb
  have h3 (q : Pattern) (ha : d17364 q = 1) (hb : d175271 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17364, d175271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17364, d175271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39325 q ha hb
  have h4 (q : Pattern) (ha : d128414 q = 1) (hb : d175272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128414, d175272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128414, d175272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128415 q = 1) (hb : d175273 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128415, d175273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128415, d175273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128416 q = 1) (hb : d175274 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128416, d175274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128416, d175274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175275 q = 1) (hb : d175394 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175275, d175394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d175275, d175394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d175276 q = 1) (hb : d175395 q = 1) : d175495 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175276, d175395, d175495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175276, d175395, d175495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39339 (p : Pattern) (ha : d175282 p = 1) (hb : d175401 p = 1) : d175501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175277 q = 1) (hb : d175396 q = 1) : d175496 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175277, d175396, d175496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175277, d175396, d175496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39338 q ha hb
  have h2 (q : Pattern) (ha : d175278 q = 1) (hb : d175397 q = 1) : d175497 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175278, d175397, d175497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175278, d175397, d175497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175279 q = 1) (hb : d175398 q = 1) : d175498 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175279, d175398, d175498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175279, d175398, d175498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175280 q = 1) (hb : d175399 q = 1) : d175499 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175280, d175399, d175499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175280, d175399, d175499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d175281 q = 1) (hb : d175400 q = 1) : d175500 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175281, d175400, d175500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175281, d175400, d175500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175282 q = 1) (hb : d175401 q = 1) : d175501 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175282, d175401, d175501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175282, d175401, d175501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39340 (p : Pattern) (ha : d175288 p = 1) (hb : d175407 p = 1) : d175507 p = 1 := by
  have h0 (q : Pattern) (ha : d174829 q = 1) (hb : d175360 q = 1) : d175464 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d174829, d175360, d175464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39253 q ha hb
    | true =>
      simp only [d174829, d175360, d175464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39266 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d174915 q = 1) (hb : d175369 q = 1) : d175472 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d174915, d175369, d175472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d174915, d175369, d175472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39282 q ha hb
  have h3 (q : Pattern) (ha : d174916 q = 1) (hb : d175370 q = 1) : d175473 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d174916, d175370, d175473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d174916, d175370, d175473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175037 q = 1) (hb : d175379 q = 1) : d175481 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d175037, d175379, d175481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175037, d175379, d175481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39301 q ha hb
  have h5 (q : Pattern) (ha : d175038 q = 1) (hb : d175380 q = 1) : d175482 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d175038, d175380, d175482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175038, d175380, d175482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175039 q = 1) (hb : d175381 q = 1) : d175483 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d175039, d175381, d175483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175039, d175381, d175483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d175161 q = 1) (hb : d175390 q = 1) : d175491 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d175161, d175390, d175491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175161, d175390, d175491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39320 q ha hb
  have h8 (q : Pattern) (ha : d175162 q = 1) (hb : d175391 q = 1) : d175492 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d175162, d175391, d175492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175162, d175391, d175492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d175163 q = 1) (hb : d175392 q = 1) : d175493 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d175163, d175392, d175493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175163, d175392, d175493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d175164 q = 1) (hb : d175393 q = 1) : d175494 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d175164, d175393, d175494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d175164, d175393, d175494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d175283 q = 1) (hb : d175402 q = 1) : d175502 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d175283, d175402, d175502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175283, d175402, d175502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39339 q ha hb
  have h12 (q : Pattern) (ha : d175284 q = 1) (hb : d175403 q = 1) : d175503 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d175284, d175403, d175503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175284, d175403, d175503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d175285 q = 1) (hb : d175404 q = 1) : d175504 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d175285, d175404, d175504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175285, d175404, d175504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d175286 q = 1) (hb : d175405 q = 1) : d175505 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d175286, d175405, d175505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175286, d175405, d175505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d175287 q = 1) (hb : d175406 q = 1) : d175506 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d175287, d175406, d175506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d175287, d175406, d175506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d175288 q = 1) (hb : d175407 q = 1) : d175507 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d175288, d175407, d175507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d175288, d175407, d175507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro39341 (p : Pattern) (ha : d175294 p = 1) (hb : d175413 p = 1) : d175513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175289 q = 1) (hb : d175408 q = 1) : d175508 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d175289, d175408, d175508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39340 q ha hb
    | true =>
      simp only [d175289, d175408, d175508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175290 q = 1) (hb : d175409 q = 1) : d175509 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d175290, d175409, d175509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175290, d175409, d175509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175291 q = 1) (hb : d175410 q = 1) : d175510 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d175291, d175410, d175510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175291, d175410, d175510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175292 q = 1) (hb : d175411 q = 1) : d175511 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d175292, d175411, d175511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175292, d175411, d175511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175293 q = 1) (hb : d175412 q = 1) : d175512 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d175293, d175412, d175512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175293, d175412, d175512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175294 q = 1) (hb : d175413 q = 1) : d175513 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d175294, d175413, d175513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175294, d175413, d175513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39342 (p : Pattern) (ha : d175300 p = 1) (hb : d175419 p = 1) : d175519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175295 q = 1) (hb : d175414 q = 1) : d175514 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d175295, d175414, d175514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39341 q ha hb
    | true =>
      simp only [d175295, d175414, d175514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175296 q = 1) (hb : d175415 q = 1) : d175515 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d175296, d175415, d175515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175296, d175415, d175515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175297 q = 1) (hb : d175416 q = 1) : d175516 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d175297, d175416, d175516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175297, d175416, d175516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175298 q = 1) (hb : d175417 q = 1) : d175517 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d175298, d175417, d175517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175298, d175417, d175517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175299 q = 1) (hb : d175418 q = 1) : d175518 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d175299, d175418, d175518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175299, d175418, d175518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175300 q = 1) (hb : d175419 q = 1) : d175519 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d175300, d175419, d175519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175300, d175419, d175519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39343 (p : Pattern) (ha : d175306 p = 1) (hb : d175425 p = 1) : d175525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175301 q = 1) (hb : d175420 q = 1) : d175520 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d175301, d175420, d175520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39342 q ha hb
    | true =>
      simp only [d175301, d175420, d175520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175302 q = 1) (hb : d175421 q = 1) : d175521 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d175302, d175421, d175521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175302, d175421, d175521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175303 q = 1) (hb : d175422 q = 1) : d175522 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d175303, d175422, d175522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175303, d175422, d175522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175304 q = 1) (hb : d175423 q = 1) : d175523 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d175304, d175423, d175523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175304, d175423, d175523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175305 q = 1) (hb : d175424 q = 1) : d175524 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d175305, d175424, d175524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175305, d175424, d175524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175306 q = 1) (hb : d175425 q = 1) : d175525 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d175306, d175425, d175525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175306, d175425, d175525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39344 (p : Pattern) (ha : d175312 p = 1) (hb : d175431 p = 1) : d175531 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175307 q = 1) (hb : d175426 q = 1) : d175526 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d175307, d175426, d175526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39343 q ha hb
    | true =>
      simp only [d175307, d175426, d175526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175308 q = 1) (hb : d175427 q = 1) : d175527 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d175308, d175427, d175527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175308, d175427, d175527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175309 q = 1) (hb : d175428 q = 1) : d175528 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d175309, d175428, d175528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175309, d175428, d175528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175310 q = 1) (hb : d175429 q = 1) : d175529 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d175310, d175429, d175529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175310, d175429, d175529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175311 q = 1) (hb : d175430 q = 1) : d175530 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d175311, d175430, d175530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175311, d175430, d175530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175312 q = 1) (hb : d175431 q = 1) : d175531 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d175312, d175431, d175531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175312, d175431, d175531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39345 (p : Pattern) (ha : d175318 p = 1) (hb : d175437 p = 1) : d175537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175313 q = 1) (hb : d175432 q = 1) : d175532 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d175313, d175432, d175532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39344 q ha hb
    | true =>
      simp only [d175313, d175432, d175532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175314 q = 1) (hb : d175433 q = 1) : d175533 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d175314, d175433, d175533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175314, d175433, d175533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175315 q = 1) (hb : d175434 q = 1) : d175534 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d175315, d175434, d175534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175315, d175434, d175534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175316 q = 1) (hb : d175435 q = 1) : d175535 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d175316, d175435, d175535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175316, d175435, d175535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175317 q = 1) (hb : d175436 q = 1) : d175536 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d175317, d175436, d175536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175317, d175436, d175536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175318 q = 1) (hb : d175437 q = 1) : d175537 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d175318, d175437, d175537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175318, d175437, d175537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39346 (p : Pattern) (ha : d175324 p = 1) (hb : d175443 p = 1) : d175543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175319 q = 1) (hb : d175438 q = 1) : d175538 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d175319, d175438, d175538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39345 q ha hb
    | true =>
      simp only [d175319, d175438, d175538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175320 q = 1) (hb : d175439 q = 1) : d175539 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d175320, d175439, d175539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175320, d175439, d175539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175321 q = 1) (hb : d175440 q = 1) : d175540 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d175321, d175440, d175540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175321, d175440, d175540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175322 q = 1) (hb : d175441 q = 1) : d175541 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d175322, d175441, d175541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175322, d175441, d175541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175323 q = 1) (hb : d175442 q = 1) : d175542 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d175323, d175442, d175542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175323, d175442, d175542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175324 q = 1) (hb : d175443 q = 1) : d175543 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d175324, d175443, d175543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175324, d175443, d175543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39347 (p : Pattern) (ha : d175330 p = 1) (hb : d175449 p = 1) : d175549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175325 q = 1) (hb : d175444 q = 1) : d175544 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d175325, d175444, d175544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39346 q ha hb
    | true =>
      simp only [d175325, d175444, d175544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175326 q = 1) (hb : d175445 q = 1) : d175545 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d175326, d175445, d175545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175326, d175445, d175545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175327 q = 1) (hb : d175446 q = 1) : d175546 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d175327, d175446, d175546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175327, d175446, d175546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175328 q = 1) (hb : d175447 q = 1) : d175547 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d175328, d175447, d175547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175328, d175447, d175547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175329 q = 1) (hb : d175448 q = 1) : d175548 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d175329, d175448, d175548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175329, d175448, d175548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175330 q = 1) (hb : d175449 q = 1) : d175549 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d175330, d175449, d175549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175330, d175449, d175549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39348 (p : Pattern) (ha : d53647 p = 1) (hb : d173704 p = 1) : d175551 p = 1 := by
  have h0 (q : Pattern) (ha : d53642 q = 1) (hb : d173704 q = 1) : d53642 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d463 q = 1) (hb : d173704 q = 1) : d407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d463, d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39134 q ha hb
  have h3 (q : Pattern) (ha : d53643 q = 1) (hb : d173704 q = 1) : d53639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53643, d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d53644 q = 1) (hb : d173704 q = 1) : d53640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53644, d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d53645 q = 1) (hb : d173704 q = 1) : d53641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53645, d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d53646 q = 1) (hb : d173704 q = 1) : d175550 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d175550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53646, d175550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53647 q = 1) (hb : d173704 q = 1) : d175551 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d175551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53647, d175551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39349 (p : Pattern) (ha : d53665 p = 1) (hb : d173704 p = 1) : d53655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d173704 q = 1) : d204 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39131 q ha hb
    | true =>
      simp only [d244, d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39126 q ha hb
  have h2 (q : Pattern) (ha : d53661 q = 1) (hb : d173704 q = 1) : d287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53662 q = 1) (hb : d173704 q = 1) : d288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53662, d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53663 q = 1) (hb : d173704 q = 1) : d289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53664 q = 1) (hb : d173704 q = 1) : d290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53665 q = 1) (hb : d173704 q = 1) : d53655 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39350 (p : Pattern) (ha : d53671 p = 1) (hb : d173704 p = 1) : d175558 p = 1 := by
  have h0 (q : Pattern) (ha : d53660 q = 1) (hb : d173704 q = 1) : d53660 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53666 q = 1) (hb : d173704 q = 1) : d53656 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53666, d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39349 q ha hb
  have h3 (q : Pattern) (ha : d53667 q = 1) (hb : d173704 q = 1) : d53657 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53667, d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d53668 q = 1) (hb : d173704 q = 1) : d53658 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53668, d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d53669 q = 1) (hb : d173704 q = 1) : d53659 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53669, d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d53670 q = 1) (hb : d173704 q = 1) : d175557 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d175557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53670, d175557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53671 q = 1) (hb : d173704 q = 1) : d175558 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d175558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53671, d175558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39351 (p : Pattern) (ha : d53677 p = 1) (hb : d173704 p = 1) : d175564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d173704 q = 1) : d175552 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d175552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, d175552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39348 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d173704 q = 1) : d175553 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d175553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, d175553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d173704 q = 1) : d175554 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d175554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, d175554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d173704 q = 1) : d175555 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d175555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, d175555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d173704 q = 1) : d175556 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d175556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d175556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d173704 q = 1) : d175559 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d175559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d175559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39350 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d173704 q = 1) : d175560 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d175560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d175560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d173704 q = 1) : d175561 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d175561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d175561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d173704 q = 1) : d175562 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d175562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d175562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d173704 q = 1) : d175563 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d175563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d175563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d173704 q = 1) : d175564 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d175564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d175564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39352 (p : Pattern) (ha : d171089 p = 1) (hb : d173704 p = 1) : d171078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171084 q = 1) (hb : d173704 q = 1) : d16052 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171084, d16052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39150 q ha hb
    | true =>
      simp only [d171084, d16052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39143 q ha hb
  have h2 (q : Pattern) (ha : d171085 q = 1) (hb : d173704 q = 1) : d16053 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171085, d16053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171085, d16053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171086 q = 1) (hb : d173704 q = 1) : d16054 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171086, d16054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171086, d16054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171087 q = 1) (hb : d173704 q = 1) : d16055 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171087, d16055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171087, d16055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171088 q = 1) (hb : d173704 q = 1) : d16056 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171088, d16056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171088, d16056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171089 q = 1) (hb : d173704 q = 1) : d171078 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171089, d171078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171089, d171078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39353 (p : Pattern) (ha : d171095 p = 1) (hb : d173704 p = 1) : d175566 p = 1 := by
  have h0 (q : Pattern) (ha : d171083 q = 1) (hb : d173704 q = 1) : d171083 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171090 q = 1) (hb : d173704 q = 1) : d171079 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171090, d171079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171090, d171079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39352 q ha hb
  have h3 (q : Pattern) (ha : d171091 q = 1) (hb : d173704 q = 1) : d171080 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171091, d171080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171091, d171080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d171092 q = 1) (hb : d173704 q = 1) : d171081 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171092, d171081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171092, d171081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d171093 q = 1) (hb : d173704 q = 1) : d171082 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171093, d171082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171093, d171082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171094 q = 1) (hb : d173704 q = 1) : d175565 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171094, d175565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171094, d175565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d171095 q = 1) (hb : d173704 q = 1) : d175566 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171095, d175566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171095, d175566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39354 (p : Pattern) (ha : d171101 p = 1) (hb : d173704 p = 1) : d175572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171096 q = 1) (hb : d173704 q = 1) : d175567 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171096, d175567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171096, d175567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39353 q ha hb
  have h2 (q : Pattern) (ha : d171097 q = 1) (hb : d173704 q = 1) : d175568 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171097, d175568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171097, d175568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171098 q = 1) (hb : d173704 q = 1) : d175569 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171098, d175569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171098, d175569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171099 q = 1) (hb : d173704 q = 1) : d175570 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171099, d175570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171099, d175570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171100 q = 1) (hb : d173704 q = 1) : d175571 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171100, d175571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171100, d175571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171101 q = 1) (hb : d173704 q = 1) : d175572 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171101, d175572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171101, d175572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39355 (p : Pattern) (ha : d171116 p = 1) (hb : d173704 p = 1) : d171105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171111 q = 1) (hb : d173704 q = 1) : d16249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171111, d16249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39166 q ha hb
    | true =>
      simp only [d171111, d16249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39158 q ha hb
  have h2 (q : Pattern) (ha : d171112 q = 1) (hb : d173704 q = 1) : d16250 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171112, d16250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171112, d16250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171113 q = 1) (hb : d173704 q = 1) : d16251 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171113, d16251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171113, d16251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171114 q = 1) (hb : d173704 q = 1) : d16252 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171114, d16252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171114, d16252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171115 q = 1) (hb : d173704 q = 1) : d16253 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171115, d16253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171115, d16253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171116 q = 1) (hb : d173704 q = 1) : d171105 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171116, d171105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171116, d171105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39356 (p : Pattern) (ha : d171122 p = 1) (hb : d173704 p = 1) : d175575 p = 1 := by
  have h0 (q : Pattern) (ha : d171110 q = 1) (hb : d173704 q = 1) : d171110 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171117 q = 1) (hb : d173704 q = 1) : d171106 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171117, d171106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171117, d171106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39355 q ha hb
  have h3 (q : Pattern) (ha : d171118 q = 1) (hb : d173704 q = 1) : d171107 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171118, d171107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171118, d171107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d171119 q = 1) (hb : d173704 q = 1) : d171108 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171119, d171108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171119, d171108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d171120 q = 1) (hb : d173704 q = 1) : d171109 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171120, d171109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171120, d171109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171121 q = 1) (hb : d173704 q = 1) : d175574 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171121, d175574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171121, d175574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d171122 q = 1) (hb : d173704 q = 1) : d175575 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171122, d175575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171122, d175575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39357 (p : Pattern) (ha : d171128 p = 1) (hb : d173704 p = 1) : d175581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171123 q = 1) (hb : d173704 q = 1) : d175576 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171123, d175576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171123, d175576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39356 q ha hb
  have h2 (q : Pattern) (ha : d171124 q = 1) (hb : d173704 q = 1) : d175577 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171124, d175577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171124, d175577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171125 q = 1) (hb : d173704 q = 1) : d175578 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171125, d175578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171125, d175578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171126 q = 1) (hb : d173704 q = 1) : d175579 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171126, d175579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171126, d175579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171127 q = 1) (hb : d173704 q = 1) : d175580 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171127, d175580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171127, d175580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171128 q = 1) (hb : d173704 q = 1) : d175581 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171128, d175581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171128, d175581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39358 (p : Pattern) (ha : d171140 p = 1) (hb : d173704 p = 1) : d16456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d173704 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39178 q ha hb
    | true =>
      simp only [d16673, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39172 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d173704 q = 1) : d16445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d173704 q = 1) : d16446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d173704 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39172 q ha hb
    | true =>
      simp only [d16676, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39176 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d173704 q = 1) : d16448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d173704 q = 1) : d16449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d173704 q = 1) : d16450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16693 q = 1) (hb : d173704 q = 1) : d16451 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39172 q ha hb
    | true =>
      simp only [d16693, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39171 q ha hb
  have h9 (q : Pattern) (ha : d16694 q = 1) (hb : d173704 q = 1) : d16452 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16695 q = 1) (hb : d173704 q = 1) : d16453 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16696 q = 1) (hb : d173704 q = 1) : d16454 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16696, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171139 q = 1) (hb : d173704 q = 1) : d16455 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, d16455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171139, d16455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171140 q = 1) (hb : d173704 q = 1) : d16456 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171140, d16456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171140, d16456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39359 (p : Pattern) (ha : d171146 p = 1) (hb : d173704 p = 1) : d16479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171141 q = 1) (hb : d173704 q = 1) : d16457 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171141, d16457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39358 q ha hb
    | true =>
      simp only [d171141, d16457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171142 q = 1) (hb : d173704 q = 1) : d16458 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171142, d16458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171142, d16458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d173704 q = 1) : d16461 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d16461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39173 q ha hb
    | true =>
      simp only [d16699, d16461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d173704 q = 1) : d16462 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d16462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d16462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171143 q = 1) (hb : d173704 q = 1) : d16463 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171143, d16463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171143, d16463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171144 q = 1) (hb : d173704 q = 1) : d16464 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171144, d16464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171144, d16464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171145 q = 1) (hb : d173704 q = 1) : d16465 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171145, d16465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171145, d16465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171146 q = 1) (hb : d173704 q = 1) : d16479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171146, d16479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171146, d16479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39360 (p : Pattern) (ha : d171152 p = 1) (hb : d173704 p = 1) : d171133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171147 q = 1) (hb : d173704 q = 1) : d16481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171147, d16481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39359 q ha hb
    | true =>
      simp only [d171147, d16481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39174 q ha hb
  have h2 (q : Pattern) (ha : d171148 q = 1) (hb : d173704 q = 1) : d16482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171148, d16482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171148, d16482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171149 q = 1) (hb : d173704 q = 1) : d16483 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171149, d16483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171149, d16483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171150 q = 1) (hb : d173704 q = 1) : d16484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171150, d16484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171150, d16484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171151 q = 1) (hb : d173704 q = 1) : d16485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171151, d16485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171151, d16485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171152 q = 1) (hb : d173704 q = 1) : d171133 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171152, d171133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171152, d171133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39361 (p : Pattern) (ha : d171158 p = 1) (hb : d173704 p = 1) : d175585 p = 1 := by
  have h0 (q : Pattern) (ha : d171138 q = 1) (hb : d173704 q = 1) : d171138 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171153 q = 1) (hb : d173704 q = 1) : d171134 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171153, d171134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171153, d171134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39360 q ha hb
  have h3 (q : Pattern) (ha : d171154 q = 1) (hb : d173704 q = 1) : d171135 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171154, d171135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171154, d171135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d171155 q = 1) (hb : d173704 q = 1) : d171136 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171155, d171136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171155, d171136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d171156 q = 1) (hb : d173704 q = 1) : d171137 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171156, d171137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171156, d171137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171157 q = 1) (hb : d173704 q = 1) : d175584 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171157, d175584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171157, d175584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d171158 q = 1) (hb : d173704 q = 1) : d175585 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171158, d175585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171158, d175585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39362 (p : Pattern) (ha : d171164 p = 1) (hb : d173704 p = 1) : d175591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171159 q = 1) (hb : d173704 q = 1) : d175586 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171159, d175586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171159, d175586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39361 q ha hb
  have h2 (q : Pattern) (ha : d171160 q = 1) (hb : d173704 q = 1) : d175587 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171160, d175587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171160, d175587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171161 q = 1) (hb : d173704 q = 1) : d175588 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171161, d175588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171161, d175588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171162 q = 1) (hb : d173704 q = 1) : d175589 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171162, d175589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171162, d175589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171163 q = 1) (hb : d173704 q = 1) : d175590 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171163, d175590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171163, d175590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171164 q = 1) (hb : d173704 q = 1) : d175591 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171164, d175591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171164, d175591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39363 (p : Pattern) (ha : d171177 p = 1) (hb : d173704 p = 1) : d16808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d173704 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39197 q ha hb
    | true =>
      simp only [d17033, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39191 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d173704 q = 1) : d16797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d173704 q = 1) : d16798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d173704 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39191 q ha hb
    | true =>
      simp only [d17036, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39195 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d173704 q = 1) : d16800 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d173704 q = 1) : d16801 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d173704 q = 1) : d16802 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17053 q = 1) (hb : d173704 q = 1) : d16803 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39191 q ha hb
    | true =>
      simp only [d17053, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39190 q ha hb
  have h9 (q : Pattern) (ha : d17054 q = 1) (hb : d173704 q = 1) : d16804 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d16804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d16804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17055 q = 1) (hb : d173704 q = 1) : d16805 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d16805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d16805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17056 q = 1) (hb : d173704 q = 1) : d16806 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d16806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17056, d16806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171176 q = 1) (hb : d173704 q = 1) : d16807 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171176, d16807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171176, d16807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171177 q = 1) (hb : d173704 q = 1) : d16808 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171177, d16808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171177, d16808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39364 (p : Pattern) (ha : d171183 p = 1) (hb : d173704 p = 1) : d16831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171178 q = 1) (hb : d173704 q = 1) : d16809 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171178, d16809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39363 q ha hb
    | true =>
      simp only [d171178, d16809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171179 q = 1) (hb : d173704 q = 1) : d16810 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171179, d16810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171179, d16810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d173704 q = 1) : d16813 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d16813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39192 q ha hb
    | true =>
      simp only [d17059, d16813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d173704 q = 1) : d16814 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d16814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d16814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171180 q = 1) (hb : d173704 q = 1) : d16815 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171180, d16815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171180, d16815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171181 q = 1) (hb : d173704 q = 1) : d16816 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171181, d16816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171181, d16816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171182 q = 1) (hb : d173704 q = 1) : d16817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171182, d16817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171182, d16817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171183 q = 1) (hb : d173704 q = 1) : d16831 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171183, d16831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171183, d16831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39365 (p : Pattern) (ha : d171189 p = 1) (hb : d173704 p = 1) : d171170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171184 q = 1) (hb : d173704 q = 1) : d16833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171184, d16833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39364 q ha hb
    | true =>
      simp only [d171184, d16833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39193 q ha hb
  have h2 (q : Pattern) (ha : d171185 q = 1) (hb : d173704 q = 1) : d16834 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171185, d16834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171185, d16834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171186 q = 1) (hb : d173704 q = 1) : d16835 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171186, d16835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171186, d16835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171187 q = 1) (hb : d173704 q = 1) : d16836 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171187, d16836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171187, d16836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171188 q = 1) (hb : d173704 q = 1) : d16837 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171188, d16837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171188, d16837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171189 q = 1) (hb : d173704 q = 1) : d171170 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171189, d171170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171189, d171170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39366 (p : Pattern) (ha : d171195 p = 1) (hb : d173704 p = 1) : d175596 p = 1 := by
  have h0 (q : Pattern) (ha : d171175 q = 1) (hb : d173704 q = 1) : d171175 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171190 q = 1) (hb : d173704 q = 1) : d171171 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171190, d171171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171190, d171171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39365 q ha hb
  have h3 (q : Pattern) (ha : d171191 q = 1) (hb : d173704 q = 1) : d171172 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171191, d171172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171191, d171172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d171192 q = 1) (hb : d173704 q = 1) : d171173 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171192, d171173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171192, d171173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d171193 q = 1) (hb : d173704 q = 1) : d171174 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171193, d171174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171193, d171174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171194 q = 1) (hb : d173704 q = 1) : d175595 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171194, d175595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171194, d175595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d171195 q = 1) (hb : d173704 q = 1) : d175596 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171195, d175596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171195, d175596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39367 (p : Pattern) (ha : d171201 p = 1) (hb : d173704 p = 1) : d175602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171196 q = 1) (hb : d173704 q = 1) : d175597 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171196, d175597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171196, d175597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39366 q ha hb
  have h2 (q : Pattern) (ha : d171197 q = 1) (hb : d173704 q = 1) : d175598 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171197, d175598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171197, d175598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171198 q = 1) (hb : d173704 q = 1) : d175599 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171198, d175599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171198, d175599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171199 q = 1) (hb : d173704 q = 1) : d175600 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171199, d175600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171199, d175600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171200 q = 1) (hb : d173704 q = 1) : d175601 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171200, d175601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171200, d175601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171201 q = 1) (hb : d173704 q = 1) : d175602 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171201, d175602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171201, d175602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39368 (p : Pattern) (ha : d171215 p = 1) (hb : d173704 p = 1) : d17174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d173704 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39216 q ha hb
    | true =>
      simp only [d17397, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39210 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d173704 q = 1) : d17163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d173704 q = 1) : d17164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d173704 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39210 q ha hb
    | true =>
      simp only [d17400, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39214 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d173704 q = 1) : d17166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d173704 q = 1) : d17167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d173704 q = 1) : d17168 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17417 q = 1) (hb : d173704 q = 1) : d17169 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39210 q ha hb
    | true =>
      simp only [d17417, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39209 q ha hb
  have h9 (q : Pattern) (ha : d17418 q = 1) (hb : d173704 q = 1) : d17170 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d17170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d17170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17419 q = 1) (hb : d173704 q = 1) : d17171 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d17171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d17171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17420 q = 1) (hb : d173704 q = 1) : d17172 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d17172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17420, d17172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171214 q = 1) (hb : d173704 q = 1) : d17173 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, d17173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171214, d17173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171215 q = 1) (hb : d173704 q = 1) : d17174 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171215, d17174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171215, d17174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39369 (p : Pattern) (ha : d171221 p = 1) (hb : d173704 p = 1) : d17197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171216 q = 1) (hb : d173704 q = 1) : d17175 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171216, d17175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39368 q ha hb
    | true =>
      simp only [d171216, d17175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171217 q = 1) (hb : d173704 q = 1) : d17176 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171217, d17176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171217, d17176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d173704 q = 1) : d17179 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d17179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39211 q ha hb
    | true =>
      simp only [d17423, d17179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d173704 q = 1) : d17180 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d17180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d17180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171218 q = 1) (hb : d173704 q = 1) : d17181 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171218, d17181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171218, d17181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171219 q = 1) (hb : d173704 q = 1) : d17182 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171219, d17182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171219, d17182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171220 q = 1) (hb : d173704 q = 1) : d17183 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171220, d17183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171220, d17183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171221 q = 1) (hb : d173704 q = 1) : d17197 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171221, d17197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171221, d17197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39370 (p : Pattern) (ha : d171227 p = 1) (hb : d173704 p = 1) : d171208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171222 q = 1) (hb : d173704 q = 1) : d17199 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171222, d17199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39369 q ha hb
    | true =>
      simp only [d171222, d17199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39212 q ha hb
  have h2 (q : Pattern) (ha : d171223 q = 1) (hb : d173704 q = 1) : d17200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171223, d17200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171223, d17200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171224 q = 1) (hb : d173704 q = 1) : d17201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171224, d17201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171224, d17201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171225 q = 1) (hb : d173704 q = 1) : d17202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171225, d17202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171225, d17202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171226 q = 1) (hb : d173704 q = 1) : d17203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171226, d17203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171226, d17203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171227 q = 1) (hb : d173704 q = 1) : d171208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171227, d171208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171227, d171208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39371 (p : Pattern) (ha : d171233 p = 1) (hb : d173704 p = 1) : d175608 p = 1 := by
  have h0 (q : Pattern) (ha : d171213 q = 1) (hb : d173704 q = 1) : d171213 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171228 q = 1) (hb : d173704 q = 1) : d171209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171228, d171209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171228, d171209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39370 q ha hb
  have h3 (q : Pattern) (ha : d171229 q = 1) (hb : d173704 q = 1) : d171210 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171229, d171210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171229, d171210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d171230 q = 1) (hb : d173704 q = 1) : d171211 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171230, d171211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171230, d171211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d171231 q = 1) (hb : d173704 q = 1) : d171212 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171231, d171212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171231, d171212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171232 q = 1) (hb : d173704 q = 1) : d175607 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171232, d175607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171232, d175607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d171233 q = 1) (hb : d173704 q = 1) : d175608 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171233, d175608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171233, d175608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39372 (p : Pattern) (ha : d171239 p = 1) (hb : d173704 p = 1) : d175614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171234 q = 1) (hb : d173704 q = 1) : d175609 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171234, d175609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171234, d175609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39371 q ha hb
  have h2 (q : Pattern) (ha : d171235 q = 1) (hb : d173704 q = 1) : d175610 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171235, d175610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171235, d175610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171236 q = 1) (hb : d173704 q = 1) : d175611 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171236, d175611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171236, d175611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171237 q = 1) (hb : d173704 q = 1) : d175612 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171237, d175612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171237, d175612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171238 q = 1) (hb : d173704 q = 1) : d175613 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171238, d175613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171238, d175613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171239 q = 1) (hb : d173704 q = 1) : d175614 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171239, d175614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171239, d175614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39373 (p : Pattern) (ha : d171245 p = 1) (hb : d173704 p = 1) : d175620 p = 1 := by
  have h0 (q : Pattern) (ha : d171102 q = 1) (hb : d173704 q = 1) : d175573 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, d175573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39351 q ha hb
    | true =>
      simp only [d171102, d175573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39354 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171129 q = 1) (hb : d173704 q = 1) : d175582 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171129, d175582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171129, d175582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39357 q ha hb
  have h3 (q : Pattern) (ha : d171130 q = 1) (hb : d173704 q = 1) : d175583 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171130, d175583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171130, d175583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171165 q = 1) (hb : d173704 q = 1) : d175592 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171165, d175592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171165, d175592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39362 q ha hb
  have h5 (q : Pattern) (ha : d171166 q = 1) (hb : d173704 q = 1) : d175593 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171166, d175593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171166, d175593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171167 q = 1) (hb : d173704 q = 1) : d175594 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171167, d175594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171167, d175594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d171202 q = 1) (hb : d173704 q = 1) : d175603 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171202, d175603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171202, d175603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39367 q ha hb
  have h8 (q : Pattern) (ha : d171203 q = 1) (hb : d173704 q = 1) : d175604 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171203, d175604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171203, d175604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d171204 q = 1) (hb : d173704 q = 1) : d175605 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171204, d175605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171204, d175605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171205 q = 1) (hb : d173704 q = 1) : d175606 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171205, d175606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171205, d175606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d171240 q = 1) (hb : d173704 q = 1) : d175615 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171240, d175615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171240, d175615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39372 q ha hb
  have h12 (q : Pattern) (ha : d171241 q = 1) (hb : d173704 q = 1) : d175616 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171241, d175616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171241, d175616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171242 q = 1) (hb : d173704 q = 1) : d175617 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171242, d175617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171242, d175617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d171243 q = 1) (hb : d173704 q = 1) : d175618 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171243, d175618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171243, d175618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d171244 q = 1) (hb : d173704 q = 1) : d175619 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d171244, d175619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171244, d175619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d171245 q = 1) (hb : d173704 q = 1) : d175620 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d171245, d175620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d171245, d175620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro39374 (p : Pattern) (ha : d171251 p = 1) (hb : d173704 p = 1) : d175626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171246 q = 1) (hb : d173704 q = 1) : d175621 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d171246, d175621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39373 q ha hb
    | true =>
      simp only [d171246, d175621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171247 q = 1) (hb : d173704 q = 1) : d175622 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d171247, d175622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171247, d175622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171248 q = 1) (hb : d173704 q = 1) : d175623 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d171248, d175623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171248, d175623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171249 q = 1) (hb : d173704 q = 1) : d175624 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d171249, d175624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171249, d175624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171250 q = 1) (hb : d173704 q = 1) : d175625 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d171250, d175625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171250, d175625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171251 q = 1) (hb : d173704 q = 1) : d175626 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d171251, d175626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171251, d175626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39375 (p : Pattern) (ha : d171257 p = 1) (hb : d173704 p = 1) : d175632 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171252 q = 1) (hb : d173704 q = 1) : d175627 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d171252, d175627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39374 q ha hb
    | true =>
      simp only [d171252, d175627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171253 q = 1) (hb : d173704 q = 1) : d175628 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d171253, d175628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171253, d175628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171254 q = 1) (hb : d173704 q = 1) : d175629 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d171254, d175629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171254, d175629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171255 q = 1) (hb : d173704 q = 1) : d175630 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d171255, d175630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171255, d175630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171256 q = 1) (hb : d173704 q = 1) : d175631 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d171256, d175631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171256, d175631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171257 q = 1) (hb : d173704 q = 1) : d175632 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d171257, d175632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171257, d175632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39376 (p : Pattern) (ha : d171263 p = 1) (hb : d173704 p = 1) : d175638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171258 q = 1) (hb : d173704 q = 1) : d175633 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d171258, d175633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39375 q ha hb
    | true =>
      simp only [d171258, d175633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171259 q = 1) (hb : d173704 q = 1) : d175634 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d171259, d175634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171259, d175634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171260 q = 1) (hb : d173704 q = 1) : d175635 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d171260, d175635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171260, d175635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171261 q = 1) (hb : d173704 q = 1) : d175636 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d171261, d175636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171261, d175636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171262 q = 1) (hb : d173704 q = 1) : d175637 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d171262, d175637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171262, d175637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171263 q = 1) (hb : d173704 q = 1) : d175638 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d171263, d175638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171263, d175638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39377 (p : Pattern) (ha : d171269 p = 1) (hb : d173704 p = 1) : d175644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171264 q = 1) (hb : d173704 q = 1) : d175639 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d171264, d175639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39376 q ha hb
    | true =>
      simp only [d171264, d175639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171265 q = 1) (hb : d173704 q = 1) : d175640 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d171265, d175640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171265, d175640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171266 q = 1) (hb : d173704 q = 1) : d175641 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d171266, d175641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171266, d175641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171267 q = 1) (hb : d173704 q = 1) : d175642 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d171267, d175642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171267, d175642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171268 q = 1) (hb : d173704 q = 1) : d175643 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d171268, d175643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171268, d175643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171269 q = 1) (hb : d173704 q = 1) : d175644 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d171269, d175644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171269, d175644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39378 (p : Pattern) (ha : d171275 p = 1) (hb : d173704 p = 1) : d175650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171270 q = 1) (hb : d173704 q = 1) : d175645 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d171270, d175645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39377 q ha hb
    | true =>
      simp only [d171270, d175645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171271 q = 1) (hb : d173704 q = 1) : d175646 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d171271, d175646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171271, d175646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171272 q = 1) (hb : d173704 q = 1) : d175647 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d171272, d175647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171272, d175647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171273 q = 1) (hb : d173704 q = 1) : d175648 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d171273, d175648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171273, d175648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171274 q = 1) (hb : d173704 q = 1) : d175649 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d171274, d175649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171274, d175649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171275 q = 1) (hb : d173704 q = 1) : d175650 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d171275, d175650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171275, d175650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39379 (p : Pattern) (ha : d171281 p = 1) (hb : d173704 p = 1) : d175656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171276 q = 1) (hb : d173704 q = 1) : d175651 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d171276, d175651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39378 q ha hb
    | true =>
      simp only [d171276, d175651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171277 q = 1) (hb : d173704 q = 1) : d175652 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d171277, d175652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171277, d175652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171278 q = 1) (hb : d173704 q = 1) : d175653 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d171278, d175653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171278, d175653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171279 q = 1) (hb : d173704 q = 1) : d175654 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d171279, d175654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171279, d175654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171280 q = 1) (hb : d173704 q = 1) : d175655 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d171280, d175655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171280, d175655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171281 q = 1) (hb : d173704 q = 1) : d175656 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d171281, d175656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171281, d175656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39380 (p : Pattern) (ha : d171287 p = 1) (hb : d173704 p = 1) : d175662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171282 q = 1) (hb : d173704 q = 1) : d175657 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d171282, d175657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39379 q ha hb
    | true =>
      simp only [d171282, d175657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171283 q = 1) (hb : d173704 q = 1) : d175658 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d171283, d175658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171283, d175658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171284 q = 1) (hb : d173704 q = 1) : d175659 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d171284, d175659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171284, d175659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171285 q = 1) (hb : d173704 q = 1) : d175660 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d171285, d175660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171285, d175660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171286 q = 1) (hb : d173704 q = 1) : d175661 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d171286, d175661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171286, d175661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171287 q = 1) (hb : d173704 q = 1) : d175662 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d171287, d175662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171287, d175662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39381 (p : Pattern) (ha : d406 p = 1) (hb : d174699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d174694 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d174663 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d174663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39238 q ha hb
    | true =>
      simp only [d50, d174663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d174695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d174695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d174695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d174664 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d174696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d174696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d174696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d174697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d174697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d174697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d174698 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d174698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d174698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d174699 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d174699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d174699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39382 (p : Pattern) (ha : d174705 p = 1) (hb : d175551 p = 1) : d54404 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d53642 q = 1) : d53642 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d407 q = 1) (hb : d174700 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d174700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d407, d174700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39381 q ha hb
  have h3 (q : Pattern) (ha : d53639 q = 1) (hb : d174701 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d174701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53639, d174701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d53640 q = 1) (hb : d174702 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d174702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53640, d174702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d53641 q = 1) (hb : d174703 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d174703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53641, d174703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d174704 q = 1) (hb : d175550 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174704, d175550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d174704, d175550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d174705 q = 1) (hb : d175551 q = 1) : d54404 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174705, d175551, d54404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d174705, d175551, d54404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39383 (p : Pattern) (ha : d53655 p = 1) (hb : d174739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d174728 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d174694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d174694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39243 q ha hb
    | true =>
      simp only [d204, d174694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39238 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d174729 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d174729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287, d174729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d174735 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288 q = 1) (hb : d174736 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d174736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d174736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289 q = 1) (hb : d174737 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d174737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d174737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290 q = 1) (hb : d174738 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d174738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d174738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53655 q = 1) (hb : d174739 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d174739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d174739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39384 (p : Pattern) (ha : d174751 p = 1) (hb : d175558 p = 1) : d54410 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d53660 q = 1) : d53660 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53656 q = 1) (hb : d174740 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d174740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53656, d174740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39383 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d174746 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53657 q = 1) (hb : d174747 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d174747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53657, d174747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53658 q = 1) (hb : d174748 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d174748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53658, d174748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d53659 q = 1) (hb : d174749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d174749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53659, d174749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d174750 q = 1) (hb : d175557 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174750, d175557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d174750, d175557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d174751 q = 1) (hb : d175558 q = 1) : d54410 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174751, d175558, d54410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d174751, d175558, d54410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39385 (p : Pattern) (ha : d174757 p = 1) (hb : d175564 p = 1) : d54416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d174678 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d174706 q = 1) (hb : d175552 q = 1) : d54405 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174706, d175552, d54405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d174706, d175552, d54405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39382 q ha hb
  have h3 (q : Pattern) (ha : d174707 q = 1) (hb : d175553 q = 1) : d54406 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174707, d175553, d54406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d174707, d175553, d54406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d174708 q = 1) (hb : d175554 q = 1) : d54407 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174708, d175554, d54407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d174708, d175554, d54407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d174709 q = 1) (hb : d175555 q = 1) : d54408 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174709, d175555, d54408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d174709, d175555, d54408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d174710 q = 1) (hb : d175556 q = 1) : d54409 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174710, d175556, d54409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174710, d175556, d54409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d174752 q = 1) (hb : d175559 q = 1) : d54411 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174752, d175559, d54411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d174752, d175559, d54411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39384 q ha hb
  have h8 (q : Pattern) (ha : d174753 q = 1) (hb : d175560 q = 1) : d54412 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174753, d175560, d54412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d174753, d175560, d54412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d174754 q = 1) (hb : d175561 q = 1) : d54413 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174754, d175561, d54413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d174754, d175561, d54413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d174755 q = 1) (hb : d175562 q = 1) : d54414 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174755, d175562, d54414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d174755, d175562, d54414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d174756 q = 1) (hb : d175563 q = 1) : d54415 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174756, d175563, d54415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d174756, d175563, d54415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d174757 q = 1) (hb : d175564 q = 1) : d54416 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174757, d175564, d54416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d174757, d175564, d54416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39386 (p : Pattern) (ha : d171078 p = 1) (hb : d174809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d174793 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16052 q = 1) (hb : d174798 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d174798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39258 q ha hb
    | true =>
      simp only [d16052, d174798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39255 q ha hb
  have h3 (q : Pattern) (ha : d16053 q = 1) (hb : d174799 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d174799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16053, d174799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d174805 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16054 q = 1) (hb : d174806 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d174806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16054, d174806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16055 q = 1) (hb : d174807 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d174807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d174807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16056 q = 1) (hb : d174808 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d174808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d174808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171078 q = 1) (hb : d174809 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, d174809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171078, d174809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39387 (p : Pattern) (ha : d174822 p = 1) (hb : d175566 p = 1) : d175663 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d171083 q = 1) : d171083 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171079 q = 1) (hb : d174810 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, d174810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171079, d174810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39386 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d174817 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d171080 q = 1) (hb : d174818 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, d174818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171080, d174818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171081 q = 1) (hb : d174819 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, d174819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171081, d174819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171082 q = 1) (hb : d174820 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, d174820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171082, d174820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d174821 q = 1) (hb : d175565 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174821, d175565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d174821, d175565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d174822 q = 1) (hb : d175566 q = 1) : d175663 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174822, d175566, d175663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d174822, d175566, d175663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39388 (p : Pattern) (ha : d174828 p = 1) (hb : d175572 p = 1) : d175669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d174823 q = 1) (hb : d175567 q = 1) : d175664 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174823, d175567, d175664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174823, d175567, d175664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39387 q ha hb
  have h2 (q : Pattern) (ha : d174824 q = 1) (hb : d175568 q = 1) : d175665 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174824, d175568, d175665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174824, d175568, d175665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d174825 q = 1) (hb : d175569 q = 1) : d175666 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174825, d175569, d175666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174825, d175569, d175666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d174826 q = 1) (hb : d175570 q = 1) : d175667 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174826, d175570, d175667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174826, d175570, d175667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d174827 q = 1) (hb : d175571 q = 1) : d175668 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174827, d175571, d175668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174827, d175571, d175668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d174828 q = 1) (hb : d175572 q = 1) : d175669 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174828, d175572, d175669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174828, d175572, d175669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39389 (p : Pattern) (ha : d171105 p = 1) (hb : d174895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d174879 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16249 q = 1) (hb : d174884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d174884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39274 q ha hb
    | true =>
      simp only [d16249, d174884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39270 q ha hb
  have h3 (q : Pattern) (ha : d16250 q = 1) (hb : d174885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d174885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16250, d174885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d174891 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16251 q = 1) (hb : d174892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d174892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16251, d174892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16252 q = 1) (hb : d174893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d174893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d174893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16253 q = 1) (hb : d174894 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d174894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d174894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171105 q = 1) (hb : d174895 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171105, d174895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171105, d174895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39390 (p : Pattern) (ha : d174908 p = 1) (hb : d175575 p = 1) : d175671 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d171110 q = 1) : d171110 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171106 q = 1) (hb : d174896 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171106, d174896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171106, d174896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39389 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d174903 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d171107 q = 1) (hb : d174904 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171107, d174904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171107, d174904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171108 q = 1) (hb : d174905 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171108, d174905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171108, d174905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171109 q = 1) (hb : d174906 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171109, d174906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171109, d174906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d174907 q = 1) (hb : d175574 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174907, d175574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d174907, d175574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d174908 q = 1) (hb : d175575 q = 1) : d175671 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174908, d175575, d175671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d174908, d175575, d175671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39391 (p : Pattern) (ha : d174914 p = 1) (hb : d175581 p = 1) : d175677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d174909 q = 1) (hb : d175576 q = 1) : d175672 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174909, d175576, d175672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174909, d175576, d175672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39390 q ha hb
  have h2 (q : Pattern) (ha : d174910 q = 1) (hb : d175577 q = 1) : d175673 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174910, d175577, d175673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174910, d175577, d175673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d174911 q = 1) (hb : d175578 q = 1) : d175674 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174911, d175578, d175674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174911, d175578, d175674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d174912 q = 1) (hb : d175579 q = 1) : d175675 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174912, d175579, d175675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174912, d175579, d175675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d174913 q = 1) (hb : d175580 q = 1) : d175676 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174913, d175580, d175676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174913, d175580, d175676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d174914 q = 1) (hb : d175581 q = 1) : d175677 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174914, d175581, d175677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174914, d175581, d175677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39392 (p : Pattern) (ha : d16456 p = 1) (hb : d174986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d174945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d174945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39289 q ha hb
    | true =>
      simp only [d16444, d174945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39284 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d174946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d174946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d174946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d174947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d174947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d174947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d174953 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d174953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39284 q ha hb
    | true =>
      simp only [d16447, d174953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39288 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d174954 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d174954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d174954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d174955 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d174955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d174955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d174956 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d174956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d174956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16451 q = 1) (hb : d174972 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d174972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39284 q ha hb
    | true =>
      simp only [d16451, d174972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39283 q ha hb
  have h9 (q : Pattern) (ha : d16452 q = 1) (hb : d174973 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d174973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d174973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16453 q = 1) (hb : d174974 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d174974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d174974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16454 q = 1) (hb : d174975 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d174975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16454, d174975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16455 q = 1) (hb : d174985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16455, d174985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16455, d174985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16456 q = 1) (hb : d174986 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16456, d174986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16456, d174986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39393 (p : Pattern) (ha : d16479 p = 1) (hb : d174992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d174987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d174987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39392 q ha hb
    | true =>
      simp only [d16457, d174987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d174988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d174988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d174988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d174978 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d174978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39285 q ha hb
    | true =>
      simp only [d16461, d174978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d174979 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d174979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d174979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d174989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d174989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d174989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d174990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d174990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d174990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d174991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d174991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d174991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16479 q = 1) (hb : d174992 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16479, d174992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16479, d174992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39394 (p : Pattern) (ha : d171133 p = 1) (hb : d175017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d174984 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16481 q = 1) (hb : d174997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d174997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39393 q ha hb
    | true =>
      simp only [d16481, d174997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39286 q ha hb
  have h3 (q : Pattern) (ha : d16482 q = 1) (hb : d174998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d174998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16482, d174998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d175013 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16483 q = 1) (hb : d175014 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d175014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16483, d175014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16484 q = 1) (hb : d175015 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d175015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d175015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16485 q = 1) (hb : d175016 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d175016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d175016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171133 q = 1) (hb : d175017 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171133, d175017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171133, d175017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39395 (p : Pattern) (ha : d175030 p = 1) (hb : d175585 p = 1) : d175680 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d171138 q = 1) : d171138 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171134 q = 1) (hb : d175018 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171134, d175018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171134, d175018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39394 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d175025 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d171135 q = 1) (hb : d175026 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171135, d175026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171135, d175026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171136 q = 1) (hb : d175027 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171136, d175027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171136, d175027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171137 q = 1) (hb : d175028 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171137, d175028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171137, d175028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175029 q = 1) (hb : d175584 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175029, d175584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d175029, d175584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d175030 q = 1) (hb : d175585 q = 1) : d175680 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175030, d175585, d175680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175030, d175585, d175680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39396 (p : Pattern) (ha : d175036 p = 1) (hb : d175591 p = 1) : d175686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175031 q = 1) (hb : d175586 q = 1) : d175681 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175031, d175586, d175681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175031, d175586, d175681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39395 q ha hb
  have h2 (q : Pattern) (ha : d175032 q = 1) (hb : d175587 q = 1) : d175682 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175032, d175587, d175682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175032, d175587, d175682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175033 q = 1) (hb : d175588 q = 1) : d175683 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175033, d175588, d175683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175033, d175588, d175683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175034 q = 1) (hb : d175589 q = 1) : d175684 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175034, d175589, d175684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175034, d175589, d175684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d175035 q = 1) (hb : d175590 q = 1) : d175685 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175035, d175590, d175685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175035, d175590, d175685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175036 q = 1) (hb : d175591 q = 1) : d175686 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175036, d175591, d175686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175036, d175591, d175686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39397 (p : Pattern) (ha : d16808 p = 1) (hb : d175110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d175068 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d175068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39308 q ha hb
    | true =>
      simp only [d16796, d175068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39303 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d175069 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d175069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d175069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d175070 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d175070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d175070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d175076 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d175076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39303 q ha hb
    | true =>
      simp only [d16799, d175076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39307 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d175077 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d175077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d175077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d175078 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d175078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d175078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d175079 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d175079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d175079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16803 q = 1) (hb : d175096 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d175096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39303 q ha hb
    | true =>
      simp only [d16803, d175096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39302 q ha hb
  have h9 (q : Pattern) (ha : d16804 q = 1) (hb : d175097 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d175097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d175097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16805 q = 1) (hb : d175098 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d175098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d175098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16806 q = 1) (hb : d175099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d175099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16806, d175099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16807 q = 1) (hb : d175109 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16807, d175109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16807, d175109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16808 q = 1) (hb : d175110 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16808, d175110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16808, d175110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39398 (p : Pattern) (ha : d16831 p = 1) (hb : d175116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d175111 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d175111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39397 q ha hb
    | true =>
      simp only [d16809, d175111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d175112 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d175112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d175112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d175102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d175102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39304 q ha hb
    | true =>
      simp only [d16813, d175102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d175103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d175103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d175103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d175113 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d175113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d175113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d175114 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d175114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d175114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d175115 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d175115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d175115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16831 q = 1) (hb : d175116 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16831, d175116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16831, d175116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39399 (p : Pattern) (ha : d171170 p = 1) (hb : d175141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d175108 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16833 q = 1) (hb : d175121 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, d175121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39398 q ha hb
    | true =>
      simp only [d16833, d175121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39305 q ha hb
  have h3 (q : Pattern) (ha : d16834 q = 1) (hb : d175122 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d175122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16834, d175122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d175137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16835 q = 1) (hb : d175138 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d175138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16835, d175138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16836 q = 1) (hb : d175139 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d175139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d175139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16837 q = 1) (hb : d175140 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d175140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d175140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171170 q = 1) (hb : d175141 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171170, d175141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171170, d175141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39400 (p : Pattern) (ha : d175154 p = 1) (hb : d175596 p = 1) : d175690 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d171175 q = 1) : d171175 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171171 q = 1) (hb : d175142 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171171, d175142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171171, d175142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39399 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d175149 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d171172 q = 1) (hb : d175150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171172, d175150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171172, d175150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171173 q = 1) (hb : d175151 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171173, d175151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171173, d175151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171174 q = 1) (hb : d175152 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171174, d175152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171174, d175152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175153 q = 1) (hb : d175595 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175153, d175595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d175153, d175595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d175154 q = 1) (hb : d175596 q = 1) : d175690 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175154, d175596, d175690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175154, d175596, d175690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39401 (p : Pattern) (ha : d175160 p = 1) (hb : d175602 p = 1) : d175696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175155 q = 1) (hb : d175597 q = 1) : d175691 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175155, d175597, d175691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175155, d175597, d175691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39400 q ha hb
  have h2 (q : Pattern) (ha : d175156 q = 1) (hb : d175598 q = 1) : d175692 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175156, d175598, d175692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175156, d175598, d175692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175157 q = 1) (hb : d175599 q = 1) : d175693 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175157, d175599, d175693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175157, d175599, d175693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175158 q = 1) (hb : d175600 q = 1) : d175694 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175158, d175600, d175694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175158, d175600, d175694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d175159 q = 1) (hb : d175601 q = 1) : d175695 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175159, d175601, d175695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175159, d175601, d175695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175160 q = 1) (hb : d175602 q = 1) : d175696 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175160, d175602, d175696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175160, d175602, d175696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39402 (p : Pattern) (ha : d17174 p = 1) (hb : d175232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d175190 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d175190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39327 q ha hb
    | true =>
      simp only [d17162, d175190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39322 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d175191 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d175191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d175191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d175192 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d175192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d175192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d175198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d175198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39322 q ha hb
    | true =>
      simp only [d17165, d175198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39326 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d175199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d175199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d175199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d175200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d175200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d175200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d175201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d175201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d175201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17169 q = 1) (hb : d175218 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d175218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39322 q ha hb
    | true =>
      simp only [d17169, d175218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39321 q ha hb
  have h9 (q : Pattern) (ha : d17170 q = 1) (hb : d175219 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d175219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d175219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17171 q = 1) (hb : d175220 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d175220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d175220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17172 q = 1) (hb : d175221 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d175221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17172, d175221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17173 q = 1) (hb : d175231 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17173, d175231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17173, d175231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17174 q = 1) (hb : d175232 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17174, d175232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17174, d175232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39403 (p : Pattern) (ha : d17197 p = 1) (hb : d175238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d175233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d175233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39402 q ha hb
    | true =>
      simp only [d17175, d175233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d175234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d175234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d175234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d175224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d175224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39323 q ha hb
    | true =>
      simp only [d17179, d175224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d175225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d175225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d175225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d175235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d175235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d175235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d175236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d175236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d175236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17183 q = 1) (hb : d175237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17183, d175237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17183, d175237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17197 q = 1) (hb : d175238 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17197, d175238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17197, d175238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39404 (p : Pattern) (ha : d171208 p = 1) (hb : d175263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d175230 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17199 q = 1) (hb : d175243 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, d175243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39403 q ha hb
    | true =>
      simp only [d17199, d175243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39324 q ha hb
  have h3 (q : Pattern) (ha : d17200 q = 1) (hb : d175244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d175244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17200, d175244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d175259 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17201 q = 1) (hb : d175260 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d175260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17201, d175260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17202 q = 1) (hb : d175261 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d175261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d175261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17203 q = 1) (hb : d175262 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d175262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d175262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171208 q = 1) (hb : d175263 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171208, d175263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171208, d175263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39405 (p : Pattern) (ha : d175276 p = 1) (hb : d175608 p = 1) : d175701 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d171213 q = 1) : d171213 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171209 q = 1) (hb : d175264 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171209, d175264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171209, d175264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39404 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d175271 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d171210 q = 1) (hb : d175272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171210, d175272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171210, d175272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171211 q = 1) (hb : d175273 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171211, d175273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171211, d175273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171212 q = 1) (hb : d175274 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171212, d175274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171212, d175274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175275 q = 1) (hb : d175607 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175275, d175607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d175275, d175607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d175276 q = 1) (hb : d175608 q = 1) : d175701 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175276, d175608, d175701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175276, d175608, d175701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39406 (p : Pattern) (ha : d175282 p = 1) (hb : d175614 p = 1) : d175707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175277 q = 1) (hb : d175609 q = 1) : d175702 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175277, d175609, d175702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175277, d175609, d175702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39405 q ha hb
  have h2 (q : Pattern) (ha : d175278 q = 1) (hb : d175610 q = 1) : d175703 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175278, d175610, d175703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175278, d175610, d175703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175279 q = 1) (hb : d175611 q = 1) : d175704 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175279, d175611, d175704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175279, d175611, d175704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175280 q = 1) (hb : d175612 q = 1) : d175705 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175280, d175612, d175705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175280, d175612, d175705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d175281 q = 1) (hb : d175613 q = 1) : d175706 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175281, d175613, d175706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175281, d175613, d175706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175282 q = 1) (hb : d175614 q = 1) : d175707 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175282, d175614, d175707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175282, d175614, d175707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39407 (p : Pattern) (ha : d175288 p = 1) (hb : d175620 p = 1) : d175713 p = 1 := by
  have h0 (q : Pattern) (ha : d174829 q = 1) (hb : d175573 q = 1) : d175670 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d174829, d175573, d175670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39385 q ha hb
    | true =>
      simp only [d174829, d175573, d175670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39388 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d174915 q = 1) (hb : d175582 q = 1) : d175678 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d174915, d175582, d175678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d174915, d175582, d175678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39391 q ha hb
  have h3 (q : Pattern) (ha : d174916 q = 1) (hb : d175583 q = 1) : d175679 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d174916, d175583, d175679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d174916, d175583, d175679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175037 q = 1) (hb : d175592 q = 1) : d175687 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d175037, d175592, d175687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175037, d175592, d175687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39396 q ha hb
  have h5 (q : Pattern) (ha : d175038 q = 1) (hb : d175593 q = 1) : d175688 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d175038, d175593, d175688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175038, d175593, d175688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175039 q = 1) (hb : d175594 q = 1) : d175689 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d175039, d175594, d175689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175039, d175594, d175689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d175161 q = 1) (hb : d175603 q = 1) : d175697 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d175161, d175603, d175697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175161, d175603, d175697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39401 q ha hb
  have h8 (q : Pattern) (ha : d175162 q = 1) (hb : d175604 q = 1) : d175698 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d175162, d175604, d175698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175162, d175604, d175698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d175163 q = 1) (hb : d175605 q = 1) : d175699 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d175163, d175605, d175699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175163, d175605, d175699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d175164 q = 1) (hb : d175606 q = 1) : d175700 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d175164, d175606, d175700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d175164, d175606, d175700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d175283 q = 1) (hb : d175615 q = 1) : d175708 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d175283, d175615, d175708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175283, d175615, d175708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39406 q ha hb
  have h12 (q : Pattern) (ha : d175284 q = 1) (hb : d175616 q = 1) : d175709 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d175284, d175616, d175709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175284, d175616, d175709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d175285 q = 1) (hb : d175617 q = 1) : d175710 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d175285, d175617, d175710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175285, d175617, d175710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d175286 q = 1) (hb : d175618 q = 1) : d175711 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d175286, d175618, d175711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d175286, d175618, d175711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d175287 q = 1) (hb : d175619 q = 1) : d175712 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d175287, d175619, d175712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d175287, d175619, d175712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d175288 q = 1) (hb : d175620 q = 1) : d175713 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d175288, d175620, d175713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d175288, d175620, d175713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro39408 (p : Pattern) (ha : d175294 p = 1) (hb : d175626 p = 1) : d175719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175289 q = 1) (hb : d175621 q = 1) : d175714 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d175289, d175621, d175714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39407 q ha hb
    | true =>
      simp only [d175289, d175621, d175714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175290 q = 1) (hb : d175622 q = 1) : d175715 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d175290, d175622, d175715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175290, d175622, d175715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175291 q = 1) (hb : d175623 q = 1) : d175716 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d175291, d175623, d175716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175291, d175623, d175716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175292 q = 1) (hb : d175624 q = 1) : d175717 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d175292, d175624, d175717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175292, d175624, d175717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175293 q = 1) (hb : d175625 q = 1) : d175718 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d175293, d175625, d175718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175293, d175625, d175718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175294 q = 1) (hb : d175626 q = 1) : d175719 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d175294, d175626, d175719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175294, d175626, d175719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39409 (p : Pattern) (ha : d175300 p = 1) (hb : d175632 p = 1) : d175725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175295 q = 1) (hb : d175627 q = 1) : d175720 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d175295, d175627, d175720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39408 q ha hb
    | true =>
      simp only [d175295, d175627, d175720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175296 q = 1) (hb : d175628 q = 1) : d175721 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d175296, d175628, d175721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175296, d175628, d175721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175297 q = 1) (hb : d175629 q = 1) : d175722 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d175297, d175629, d175722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175297, d175629, d175722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175298 q = 1) (hb : d175630 q = 1) : d175723 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d175298, d175630, d175723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175298, d175630, d175723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175299 q = 1) (hb : d175631 q = 1) : d175724 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d175299, d175631, d175724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175299, d175631, d175724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175300 q = 1) (hb : d175632 q = 1) : d175725 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d175300, d175632, d175725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175300, d175632, d175725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39410 (p : Pattern) (ha : d175306 p = 1) (hb : d175638 p = 1) : d175731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175301 q = 1) (hb : d175633 q = 1) : d175726 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d175301, d175633, d175726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39409 q ha hb
    | true =>
      simp only [d175301, d175633, d175726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175302 q = 1) (hb : d175634 q = 1) : d175727 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d175302, d175634, d175727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175302, d175634, d175727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175303 q = 1) (hb : d175635 q = 1) : d175728 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d175303, d175635, d175728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175303, d175635, d175728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175304 q = 1) (hb : d175636 q = 1) : d175729 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d175304, d175636, d175729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175304, d175636, d175729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175305 q = 1) (hb : d175637 q = 1) : d175730 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d175305, d175637, d175730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175305, d175637, d175730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175306 q = 1) (hb : d175638 q = 1) : d175731 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d175306, d175638, d175731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175306, d175638, d175731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39411 (p : Pattern) (ha : d175312 p = 1) (hb : d175644 p = 1) : d175737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175307 q = 1) (hb : d175639 q = 1) : d175732 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d175307, d175639, d175732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39410 q ha hb
    | true =>
      simp only [d175307, d175639, d175732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175308 q = 1) (hb : d175640 q = 1) : d175733 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d175308, d175640, d175733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175308, d175640, d175733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175309 q = 1) (hb : d175641 q = 1) : d175734 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d175309, d175641, d175734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175309, d175641, d175734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175310 q = 1) (hb : d175642 q = 1) : d175735 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d175310, d175642, d175735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175310, d175642, d175735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175311 q = 1) (hb : d175643 q = 1) : d175736 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d175311, d175643, d175736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175311, d175643, d175736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175312 q = 1) (hb : d175644 q = 1) : d175737 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d175312, d175644, d175737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175312, d175644, d175737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39412 (p : Pattern) (ha : d175318 p = 1) (hb : d175650 p = 1) : d175743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175313 q = 1) (hb : d175645 q = 1) : d175738 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d175313, d175645, d175738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39411 q ha hb
    | true =>
      simp only [d175313, d175645, d175738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175314 q = 1) (hb : d175646 q = 1) : d175739 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d175314, d175646, d175739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175314, d175646, d175739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175315 q = 1) (hb : d175647 q = 1) : d175740 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d175315, d175647, d175740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175315, d175647, d175740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175316 q = 1) (hb : d175648 q = 1) : d175741 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d175316, d175648, d175741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175316, d175648, d175741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175317 q = 1) (hb : d175649 q = 1) : d175742 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d175317, d175649, d175742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175317, d175649, d175742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175318 q = 1) (hb : d175650 q = 1) : d175743 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d175318, d175650, d175743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175318, d175650, d175743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39413 (p : Pattern) (ha : d175324 p = 1) (hb : d175656 p = 1) : d175749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175319 q = 1) (hb : d175651 q = 1) : d175744 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d175319, d175651, d175744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39412 q ha hb
    | true =>
      simp only [d175319, d175651, d175744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175320 q = 1) (hb : d175652 q = 1) : d175745 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d175320, d175652, d175745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175320, d175652, d175745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175321 q = 1) (hb : d175653 q = 1) : d175746 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d175321, d175653, d175746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175321, d175653, d175746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175322 q = 1) (hb : d175654 q = 1) : d175747 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d175322, d175654, d175747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175322, d175654, d175747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175323 q = 1) (hb : d175655 q = 1) : d175748 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d175323, d175655, d175748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175323, d175655, d175748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175324 q = 1) (hb : d175656 q = 1) : d175749 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d175324, d175656, d175749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175324, d175656, d175749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39414 (p : Pattern) (ha : d175330 p = 1) (hb : d175662 p = 1) : d175755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175325 q = 1) (hb : d175657 q = 1) : d175750 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d175325, d175657, d175750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39413 q ha hb
    | true =>
      simp only [d175325, d175657, d175750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d175326 q = 1) (hb : d175658 q = 1) : d175751 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d175326, d175658, d175751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175326, d175658, d175751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d175327 q = 1) (hb : d175659 q = 1) : d175752 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d175327, d175659, d175752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175327, d175659, d175752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d175328 q = 1) (hb : d175660 q = 1) : d175753 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d175328, d175660, d175753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175328, d175660, d175753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d175329 q = 1) (hb : d175661 q = 1) : d175754 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d175329, d175661, d175754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175329, d175661, d175754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d175330 q = 1) (hb : d175662 q = 1) : d175755 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d175330, d175662, d175755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175330, d175662, d175755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39415 (p : Pattern) (ha : d406 p = 1) (hb : d175760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173802 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d175756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d175756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d175756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d173772 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d175757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d175757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d175757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d175758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d175758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d175758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d175759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d175759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d175759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d175760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d175760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d175760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39416 (p : Pattern) (ha : d175551 p = 1) (hb : d175766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d407 q = 1) (hb : d175761 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d175761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d407, d175761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39415 q ha hb
  have h3 (q : Pattern) (ha : d53639 q = 1) (hb : d175762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d175762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53639, d175762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d53640 q = 1) (hb : d175763 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d175763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53640, d175763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d53641 q = 1) (hb : d175764 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d175764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53641, d175764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d175550 q = 1) (hb : d175765 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175550, d175765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175550, d175765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175551 q = 1) (hb : d175766 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175551, d175766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175551, d175766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39417 (p : Pattern) (ha : d53655 p = 1) (hb : d175776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173852 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d175772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d175772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287, d175772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d173875 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288 q = 1) (hb : d175773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d175773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d175773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289 q = 1) (hb : d175774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d175774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d175774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290 q = 1) (hb : d175775 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d175775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d175775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53655 q = 1) (hb : d175776 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d175776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d175776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39418 (p : Pattern) (ha : d175558 p = 1) (hb : d175782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53660 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53656 q = 1) (hb : d175777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d175777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53656, d175777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39417 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d173886 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53657 q = 1) (hb : d175778 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d175778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53657, d175778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53658 q = 1) (hb : d175779 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d175779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53658, d175779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d53659 q = 1) (hb : d175780 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d175780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53659, d175780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175557 q = 1) (hb : d175781 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175557, d175781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d175557, d175781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d175558 q = 1) (hb : d175782 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175558, d175782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175558, d175782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39419 (p : Pattern) (ha : d175564 p = 1) (hb : d175788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173786 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d175552 q = 1) (hb : d175767 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175552, d175767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175552, d175767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39416 q ha hb
  have h3 (q : Pattern) (ha : d175553 q = 1) (hb : d175768 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175553, d175768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175553, d175768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175554 q = 1) (hb : d175769 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175554, d175769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175554, d175769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d175555 q = 1) (hb : d175770 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175555, d175770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175555, d175770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175556 q = 1) (hb : d175771 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175556, d175771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175556, d175771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d175559 q = 1) (hb : d175783 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175559, d175783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175559, d175783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39418 q ha hb
  have h8 (q : Pattern) (ha : d175560 q = 1) (hb : d175784 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175560, d175784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175560, d175784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d175561 q = 1) (hb : d175785 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175561, d175785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175561, d175785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d175562 q = 1) (hb : d175786 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175562, d175786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175562, d175786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d175563 q = 1) (hb : d175787 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175563, d175787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175563, d175787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d175564 q = 1) (hb : d175788 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175564, d175788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d175564, d175788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39420 (p : Pattern) (ha : d171078 p = 1) (hb : d175793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173933 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16052 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16053 q = 1) (hb : d175789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d175789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16053, d175789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d173967 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16054 q = 1) (hb : d175790 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d175790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16054, d175790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16055 q = 1) (hb : d175791 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d175791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d175791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16056 q = 1) (hb : d175792 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d175792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d175792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171078 q = 1) (hb : d175793 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, d175793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171078, d175793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39421 (p : Pattern) (ha : d175566 p = 1) (hb : d175799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171079 q = 1) (hb : d175794 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, d175794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171079, d175794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39420 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d173983 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d171080 q = 1) (hb : d175795 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, d175795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171080, d175795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171081 q = 1) (hb : d175796 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, d175796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171081, d175796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171082 q = 1) (hb : d175797 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, d175797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171082, d175797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175565 q = 1) (hb : d175798 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175565, d175798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d175565, d175798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d175566 q = 1) (hb : d175799 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175566, d175799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175566, d175799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39422 (p : Pattern) (ha : d175572 p = 1) (hb : d175805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175567 q = 1) (hb : d175800 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175567, d175800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175567, d175800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39421 q ha hb
  have h2 (q : Pattern) (ha : d175568 q = 1) (hb : d175801 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175568, d175801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175568, d175801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175569 q = 1) (hb : d175802 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175569, d175802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175569, d175802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175570 q = 1) (hb : d175803 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175570, d175803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175570, d175803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d175571 q = 1) (hb : d175804 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175571, d175804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175571, d175804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175572 q = 1) (hb : d175805 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175572, d175805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175572, d175805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39423 (p : Pattern) (ha : d171105 p = 1) (hb : d175811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d174045 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16249 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16250 q = 1) (hb : d175807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d175807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16250, d175807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d174088 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16251 q = 1) (hb : d175808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d175808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16251, d175808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16252 q = 1) (hb : d175809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d175809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d175809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16253 q = 1) (hb : d175810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d175810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d175810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171105 q = 1) (hb : d175811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171105, d175811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171105, d175811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39424 (p : Pattern) (ha : d175575 p = 1) (hb : d175817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171110 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171106 q = 1) (hb : d175812 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171106, d175812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171106, d175812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39423 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d174104 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d171107 q = 1) (hb : d175813 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171107, d175813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171107, d175813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171108 q = 1) (hb : d175814 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171108, d175814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171108, d175814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171109 q = 1) (hb : d175815 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171109, d175815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171109, d175815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175574 q = 1) (hb : d175816 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175574, d175816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d175574, d175816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d175575 q = 1) (hb : d175817 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175575, d175817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175575, d175817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39425 (p : Pattern) (ha : d175581 p = 1) (hb : d175823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175576 q = 1) (hb : d175818 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175576, d175818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175576, d175818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39424 q ha hb
  have h2 (q : Pattern) (ha : d175577 q = 1) (hb : d175819 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175577, d175819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175577, d175819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175578 q = 1) (hb : d175820 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175578, d175820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175578, d175820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175579 q = 1) (hb : d175821 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175579, d175821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175579, d175821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d175580 q = 1) (hb : d175822 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175580, d175822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175580, d175822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175581 q = 1) (hb : d175823 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175581, d175823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175581, d175823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39426 (p : Pattern) (ha : d171133 p = 1) (hb : d175830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d174185 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16481 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16482 q = 1) (hb : d175826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d175826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16482, d175826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d174248 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16483 q = 1) (hb : d175827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d175827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16483, d175827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16484 q = 1) (hb : d175828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d175828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d175828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16485 q = 1) (hb : d175829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d175829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d175829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171133 q = 1) (hb : d175830 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171133, d175830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171133, d175830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39427 (p : Pattern) (ha : d175585 p = 1) (hb : d175836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171138 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171134 q = 1) (hb : d175831 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171134, d175831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171134, d175831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39426 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d174264 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d171135 q = 1) (hb : d175832 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171135, d175832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171135, d175832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171136 q = 1) (hb : d175833 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171136, d175833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171136, d175833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171137 q = 1) (hb : d175834 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171137, d175834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171137, d175834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175584 q = 1) (hb : d175835 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175584, d175835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d175584, d175835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d175585 q = 1) (hb : d175836 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175585, d175836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175585, d175836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39428 (p : Pattern) (ha : d175591 p = 1) (hb : d175842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175586 q = 1) (hb : d175837 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175586, d175837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175586, d175837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39427 q ha hb
  have h2 (q : Pattern) (ha : d175587 q = 1) (hb : d175838 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175587, d175838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175587, d175838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175588 q = 1) (hb : d175839 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175588, d175839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175588, d175839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175589 q = 1) (hb : d175840 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175589, d175840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175589, d175840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d175590 q = 1) (hb : d175841 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175590, d175841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175590, d175841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175591 q = 1) (hb : d175842 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175591, d175842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175591, d175842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39429 (p : Pattern) (ha : d171170 p = 1) (hb : d175850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d174347 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16833 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16834 q = 1) (hb : d175846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d175846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16834, d175846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d174411 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16835 q = 1) (hb : d175847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d175847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16835, d175847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16836 q = 1) (hb : d175848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d175848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d175848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16837 q = 1) (hb : d175849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d175849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d175849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171170 q = 1) (hb : d175850 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171170, d175850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171170, d175850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39430 (p : Pattern) (ha : d175596 p = 1) (hb : d175856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171175 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171171 q = 1) (hb : d175851 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171171, d175851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171171, d175851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39429 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d174427 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d171172 q = 1) (hb : d175852 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171172, d175852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171172, d175852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171173 q = 1) (hb : d175853 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171173, d175853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171173, d175853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171174 q = 1) (hb : d175854 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171174, d175854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171174, d175854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175595 q = 1) (hb : d175855 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175595, d175855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d175595, d175855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d175596 q = 1) (hb : d175856 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175596, d175856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175596, d175856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39431 (p : Pattern) (ha : d175602 p = 1) (hb : d175862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175597 q = 1) (hb : d175857 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175597, d175857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175597, d175857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39430 q ha hb
  have h2 (q : Pattern) (ha : d175598 q = 1) (hb : d175858 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175598, d175858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175598, d175858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175599 q = 1) (hb : d175859 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175599, d175859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175599, d175859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175600 q = 1) (hb : d175860 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175600, d175860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175600, d175860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d175601 q = 1) (hb : d175861 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175601, d175861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175601, d175861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175602 q = 1) (hb : d175862 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175602, d175862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175602, d175862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39432 (p : Pattern) (ha : d171208 p = 1) (hb : d175871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d174508 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17199 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17200 q = 1) (hb : d175867 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d175867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17200, d175867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d174572 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17201 q = 1) (hb : d175868 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d175868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17201, d175868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17202 q = 1) (hb : d175869 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d175869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d175869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17203 q = 1) (hb : d175870 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d175870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d175870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171208 q = 1) (hb : d175871 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171208, d175871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171208, d175871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39433 (p : Pattern) (ha : d175608 p = 1) (hb : d175877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171209 q = 1) (hb : d175872 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171209, d175872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171209, d175872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39432 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d174588 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d171210 q = 1) (hb : d175873 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171210, d175873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171210, d175873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171211 q = 1) (hb : d175874 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171211, d175874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171211, d175874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d171212 q = 1) (hb : d175875 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171212, d175875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171212, d175875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d175607 q = 1) (hb : d175876 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175607, d175876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d175607, d175876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d175608 q = 1) (hb : d175877 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175608, d175877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175608, d175877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39434 (p : Pattern) (ha : d175614 p = 1) (hb : d175883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175609 q = 1) (hb : d175878 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175609, d175878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175609, d175878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39433 q ha hb
  have h2 (q : Pattern) (ha : d175610 q = 1) (hb : d175879 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175610, d175879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175610, d175879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175611 q = 1) (hb : d175880 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175611, d175880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175611, d175880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175612 q = 1) (hb : d175881 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175612, d175881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175612, d175881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d175613 q = 1) (hb : d175882 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175613, d175882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175613, d175882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175614 q = 1) (hb : d175883 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175614, d175883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175614, d175883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39435 (p : Pattern) (ha : d175620 p = 1) (hb : d175889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d175573 q = 1) (hb : d175806 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d175573, d175806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39419 q ha hb
    | true =>
      simp only [d175573, d175806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39422 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d175582 q = 1) (hb : d175824 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d175582, d175824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175582, d175824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39425 q ha hb
  have h3 (q : Pattern) (ha : d175583 q = 1) (hb : d175825 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d175583, d175825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d175583, d175825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175592 q = 1) (hb : d175843 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d175592, d175843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175592, d175843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39428 q ha hb
  have h5 (q : Pattern) (ha : d175593 q = 1) (hb : d175844 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d175593, d175844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175593, d175844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175594 q = 1) (hb : d175845 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d175594, d175845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175594, d175845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d175603 q = 1) (hb : d175863 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d175603, d175863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175603, d175863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39431 q ha hb
  have h8 (q : Pattern) (ha : d175604 q = 1) (hb : d175864 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d175604, d175864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175604, d175864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d175605 q = 1) (hb : d175865 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d175605, d175865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175605, d175865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d175606 q = 1) (hb : d175866 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d175606, d175866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d175606, d175866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d175615 q = 1) (hb : d175884 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d175615, d175884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175615, d175884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39434 q ha hb
  have h12 (q : Pattern) (ha : d175616 q = 1) (hb : d175885 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d175616, d175885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175616, d175885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d175617 q = 1) (hb : d175886 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d175617, d175886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175617, d175886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d175618 q = 1) (hb : d175887 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d175618, d175887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175618, d175887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d175619 q = 1) (hb : d175888 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d175619, d175888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d175619, d175888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d175620 q = 1) (hb : d175889 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d175620, d175889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d175620, d175889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro39436 (p : Pattern) (ha : d175626 p = 1) (hb : d175895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175621 q = 1) (hb : d175890 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d175621, d175890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39435 q ha hb
    | true =>
      simp only [d175621, d175890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d175622 q = 1) (hb : d175891 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d175622, d175891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175622, d175891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d175623 q = 1) (hb : d175892 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d175623, d175892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175623, d175892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d175624 q = 1) (hb : d175893 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d175624, d175893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175624, d175893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d175625 q = 1) (hb : d175894 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d175625, d175894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175625, d175894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d175626 q = 1) (hb : d175895 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d175626, d175895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175626, d175895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39437 (p : Pattern) (ha : d175632 p = 1) (hb : d175901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175627 q = 1) (hb : d175896 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d175627, d175896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39436 q ha hb
    | true =>
      simp only [d175627, d175896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d175628 q = 1) (hb : d175897 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d175628, d175897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175628, d175897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d175629 q = 1) (hb : d175898 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d175629, d175898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175629, d175898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d175630 q = 1) (hb : d175899 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d175630, d175899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175630, d175899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d175631 q = 1) (hb : d175900 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d175631, d175900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175631, d175900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d175632 q = 1) (hb : d175901 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d175632, d175901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175632, d175901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39438 (p : Pattern) (ha : d175638 p = 1) (hb : d175907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175633 q = 1) (hb : d175902 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d175633, d175902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39437 q ha hb
    | true =>
      simp only [d175633, d175902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d175634 q = 1) (hb : d175903 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d175634, d175903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175634, d175903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d175635 q = 1) (hb : d175904 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d175635, d175904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175635, d175904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d175636 q = 1) (hb : d175905 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d175636, d175905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175636, d175905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d175637 q = 1) (hb : d175906 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d175637, d175906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175637, d175906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d175638 q = 1) (hb : d175907 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d175638, d175907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175638, d175907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39439 (p : Pattern) (ha : d175644 p = 1) (hb : d175913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175639 q = 1) (hb : d175908 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d175639, d175908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39438 q ha hb
    | true =>
      simp only [d175639, d175908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d175640 q = 1) (hb : d175909 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d175640, d175909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175640, d175909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d175641 q = 1) (hb : d175910 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d175641, d175910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175641, d175910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d175642 q = 1) (hb : d175911 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d175642, d175911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175642, d175911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d175643 q = 1) (hb : d175912 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d175643, d175912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175643, d175912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d175644 q = 1) (hb : d175913 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d175644, d175913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175644, d175913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39440 (p : Pattern) (ha : d175650 p = 1) (hb : d175919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175645 q = 1) (hb : d175914 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d175645, d175914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39439 q ha hb
    | true =>
      simp only [d175645, d175914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d175646 q = 1) (hb : d175915 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d175646, d175915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175646, d175915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d175647 q = 1) (hb : d175916 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d175647, d175916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175647, d175916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d175648 q = 1) (hb : d175917 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d175648, d175917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175648, d175917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d175649 q = 1) (hb : d175918 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d175649, d175918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175649, d175918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d175650 q = 1) (hb : d175919 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d175650, d175919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175650, d175919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39441 (p : Pattern) (ha : d175656 p = 1) (hb : d175925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175651 q = 1) (hb : d175920 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d175651, d175920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39440 q ha hb
    | true =>
      simp only [d175651, d175920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d175652 q = 1) (hb : d175921 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d175652, d175921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175652, d175921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d175653 q = 1) (hb : d175922 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d175653, d175922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175653, d175922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d175654 q = 1) (hb : d175923 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d175654, d175923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175654, d175923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d175655 q = 1) (hb : d175924 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d175655, d175924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175655, d175924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d175656 q = 1) (hb : d175925 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d175656, d175925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175656, d175925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39442 (p : Pattern) (ha : d175662 p = 1) (hb : d175931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175657 q = 1) (hb : d175926 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d175657, d175926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39441 q ha hb
    | true =>
      simp only [d175657, d175926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d175658 q = 1) (hb : d175927 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d175658, d175927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d175658, d175927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d175659 q = 1) (hb : d175928 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d175659, d175928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d175659, d175928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d175660 q = 1) (hb : d175929 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d175660, d175929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175660, d175929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d175661 q = 1) (hb : d175930 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d175661, d175930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d175661, d175930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d175662 q = 1) (hb : d175931 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d175662, d175931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d175662, d175931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39443 (p : Pattern) (ha : d144 p = 1) (hb : d129471 p = 1) : d13981 p = 1 := by
  have h0 (q : Pattern) (ha : d142 q = 1) (hb : d100904 q = 1) : d142 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d143 q = 1) (hb : d129471 q = 1) : d13980 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d129471, d13980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d143, d129471, d13980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d29 q = 1) (hb : d129471 q = 1) : d29 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d144 q = 1) (hb : d129471 q = 1) : d13981 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d13981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144, d13981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39444 (p : Pattern) (ha : d150 p = 1) (hb : d129471 p = 1) : d13987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d129471 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d129471 q = 1) : d13982 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39443 q ha hb
    | true =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d129471 q = 1) : d13983 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d129471 q = 1) : d13984 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d129471 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d129471 q = 1) : d13985 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d129471 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d129471 q = 1) : d13986 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d13986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d13986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d129471 q = 1) : d13987 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d13987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d13987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro39445 (p : Pattern) (ha : d203 p = 1) (hb : d129471 p = 1) : d14000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d129471 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39444 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d129471 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d129471 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d129471 q = 1) : d13990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d129471 q = 1) : d13991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d129471 q = 1) : d13992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d129471 q = 1) : d14000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d14000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d14000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39446 (p : Pattern) (ha : d4349 p = 1) (hb : d129471 p = 1) : d125429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d129471 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d129471 q = 1) : d14001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39445 q ha hb
    | true =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d129471 q = 1) : d125418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d129471 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d129471 q = 1) : d125419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d129471 q = 1) : d125427 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d129471 q = 1) : d125428 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d129471 q = 1) : d125429 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39447 (p : Pattern) (ha : d231 p = 1) (hb : d129471 p = 1) : d14020 p = 1 := by
  have h0 (q : Pattern) (ha : d229 q = 1) (hb : d100904 q = 1) : d229 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d230 q = 1) (hb : d129471 q = 1) : d14019 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d129471, d14019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d230, d129471, d14019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70 q = 1) (hb : d129471 q = 1) : d70 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d231 q = 1) (hb : d129471 q = 1) : d14020 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d14020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231, d14020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39448 (p : Pattern) (ha : d237 p = 1) (hb : d129471 p = 1) : d14026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d129471 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d129471 q = 1) : d14021 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39447 q ha hb
    | true =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d129471 q = 1) : d14022 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d129471 q = 1) : d14023 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d129471 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d129471 q = 1) : d14024 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d129471 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d129471 q = 1) : d14025 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d14025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d14025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d129471 q = 1) : d14026 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d14026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d14026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro39449 (p : Pattern) (ha : d243 p = 1) (hb : d129471 p = 1) : d14032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d129471 q = 1) : d14027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39448 q ha hb
    | true =>
      simp only [d238, d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d129471 q = 1) : d14028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d129471 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d129471 q = 1) : d14029 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d14029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d14029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d129471 q = 1) : d14030 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d14030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d14030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d129471 q = 1) : d14031 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d14031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d14031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d129471 q = 1) : d14032 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d14032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d14032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39450 (p : Pattern) (ha : d4359 p = 1) (hb : d129471 p = 1) : d125439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d129471 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d129471 q = 1) : d14033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39449 q ha hb
    | true =>
      simp only [d244, d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d129471 q = 1) : d125435 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d129471 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d129471 q = 1) : d125436 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d129471 q = 1) : d125437 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d129471 q = 1) : d125438 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d129471 q = 1) : d125439 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39451 (p : Pattern) (ha : d156 p = 1) (hb : d129471 p = 1) : d13993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d129471 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39444 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d129471 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d129471 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d129471 q = 1) : d13990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d129471 q = 1) : d13991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d129471 q = 1) : d13992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d129471 q = 1) : d13993 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d13993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d13993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39452 (p : Pattern) (ha : d51643 p = 1) (hb : d129471 p = 1) : d125417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d129471 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d129471 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d129471 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d129471 q = 1) : d13994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39451 q ha hb
    | true =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d129471 q = 1) : d125413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d129471 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d129471 q = 1) : d125414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d129471 q = 1) : d125415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d129471 q = 1) : d125416 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d129471 q = 1) : d125417 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro39453 (p : Pattern) (ha : d51646 p = 1) (hb : d129471 p = 1) : d125422 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d129471 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d129471 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d129471 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d129471 q = 1) : d13994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39451 q ha hb
    | true =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d129471 q = 1) : d125413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d129471 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d129471 q = 1) : d125414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d129471 q = 1) : d125415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d129471 q = 1) : d125416 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d129471 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d129471 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d129471 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d129471 q = 1) : d14001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39445 q ha hb
    | true =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d129471 q = 1) : d125418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d129471 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d129471 q = 1) : d125419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d129471 q = 1) : d125420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d129471 q = 1) : d125421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d129471 q = 1) : d125422 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro39454 (p : Pattern) (ha : d51652 p = 1) (hb : d129471 p = 1) : d125445 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d129471 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d129471 q = 1) : d125423 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39452 q ha hb
    | true =>
      simp only [d51647, d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39453 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d129471 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d129471 q = 1) : d125424 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d129471 q = 1) : d125425 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d129471 q = 1) : d125426 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d129471 q = 1) : d125430 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39446 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d129471 q = 1) : d125431 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d129471 q = 1) : d125432 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d129471 q = 1) : d125433 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d129471 q = 1) : d125434 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d129471 q = 1) : d125440 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39450 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d129471 q = 1) : d125441 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d129471 q = 1) : d125442 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d129471 q = 1) : d125443 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d129471 q = 1) : d125444 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d129471 q = 1) : d125445 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro39455 (p : Pattern) (ha : d284 p = 1) (hb : d129471 p = 1) : d14054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d129471 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d129471 q = 1) : d13994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39451 q ha hb
    | true =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d129471 q = 1) : d14050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d129471 q = 1) : d14051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d129471 q = 1) : d14052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d129471 q = 1) : d14053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d129471 q = 1) : d14054 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d14054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d14054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39456 (p : Pattern) (ha : d291 p = 1) (hb : d129471 p = 1) : d14061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d129471 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d129471 q = 1) : d13994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39451 q ha hb
    | true =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d129471 q = 1) : d14050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d129471 q = 1) : d14051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d129471 q = 1) : d14052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d129471 q = 1) : d14053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d129471 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d129471 q = 1) : d14001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39445 q ha hb
    | true =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d129471 q = 1) : d14057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d129471 q = 1) : d14058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d129471 q = 1) : d14059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d129471 q = 1) : d14060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d129471 q = 1) : d14061 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d14061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d14061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39457 (p : Pattern) (ha : d397 p = 1) (hb : d129471 p = 1) : d14141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d129471 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d129471 q = 1) : d13994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39451 q ha hb
    | true =>
      simp only [d157, d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d129471 q = 1) : d14050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d129471 q = 1) : d14051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d129471 q = 1) : d14052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d129471 q = 1) : d14053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d129471 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d129471 q = 1) : d14141 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d14141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d14141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39458 (p : Pattern) (ha : d296 p = 1) (hb : d129471 p = 1) : d14066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d129471 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39444 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d129471 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d129471 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d129471 q = 1) : d13990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d129471 q = 1) : d13991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d129471 q = 1) : d14065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d129471 q = 1) : d14066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d14066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d14066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39459 (p : Pattern) (ha : d303 p = 1) (hb : d129471 p = 1) : d14073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d129471 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39444 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d129471 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d129471 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d129471 q = 1) : d13990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d129471 q = 1) : d14071 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d129471 q = 1) : d14072 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d129471 q = 1) : d14073 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d14073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d14073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39460 (p : Pattern) (ha : d4736 p = 1) (hb : d129471 p = 1) : d14112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d129471 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39444 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d129471 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d129471 q = 1) : d14109 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d129471 q = 1) : d14110 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d129471 q = 1) : d14111 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d129471 q = 1) : d14112 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d14112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d14112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39461 (p : Pattern) (ha : d15966 p = 1) (hb : d129471 p = 1) : d14079 p = 1 := by
  have h0 (q : Pattern) (ha : d322 q = 1) (hb : d100904 q = 1) : d322 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d323 q = 1) (hb : d129471 q = 1) : d14077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d129471, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d323, d129471, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12494 q = 1) (hb : d100904 q = 1) : d12494 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12495 q = 1) (hb : d129471 q = 1) : d14078 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d129471, d14078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12495, d129471, d14078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15966 q = 1) (hb : d129471 q = 1) : d14079 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d14079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15966, d14079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39462 (p : Pattern) (ha : d15972 p = 1) (hb : d129471 p = 1) : d14085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d129471 q = 1) : d14080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39461 q ha hb
    | true =>
      simp only [d15967, d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39443 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d129471 q = 1) : d14081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d129471 q = 1) : d14082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d129471 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d129471 q = 1) : d13982 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39443 q ha hb
    | true =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d129471 q = 1) : d13983 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d129471 q = 1) : d13984 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d129471 q = 1) : d14083 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d129471 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d129471 q = 1) : d13985 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15971 q = 1) (hb : d129471 q = 1) : d14084 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d14084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15971, d14084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15972 q = 1) (hb : d129471 q = 1) : d14085 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d14085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15972, d14085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro39463 (p : Pattern) (ha : d15978 p = 1) (hb : d129471 p = 1) : d14091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d129471 q = 1) : d14086 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39462 q ha hb
    | true =>
      simp only [d15973, d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d129471 q = 1) : d14087 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d129471 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39444 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d129471 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d129471 q = 1) : d14088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d129471 q = 1) : d14089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d129471 q = 1) : d14090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d129471 q = 1) : d14091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d14091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d14091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39464 (p : Pattern) (ha : d128195 p = 1) (hb : d129471 p = 1) : d125455 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d129471 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d129471 q = 1) : d14067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39458 q ha hb
    | true =>
      simp only [d297, d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d129471 q = 1) : d14068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d129471 q = 1) : d14069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d129471 q = 1) : d14070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d129471 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d129471 q = 1) : d14074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39459 q ha hb
    | true =>
      simp only [d304, d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d129471 q = 1) : d14075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d129471 q = 1) : d14076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d129471 q = 1) : d14092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39463 q ha hb
    | true =>
      simp only [d15979, d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39451 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d129471 q = 1) : d125451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d129471 q = 1) : d14113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39460 q ha hb
    | true =>
      simp only [d4737, d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d129471 q = 1) : d14114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d129471 q = 1) : d125452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d129471 q = 1) : d125453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d129471 q = 1) : d125454 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128195 q = 1) (hb : d129471 q = 1) : d125455 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro39465 (p : Pattern) (ha : d376 p = 1) (hb : d129471 p = 1) : d14119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d129471 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39444 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d129471 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d129471 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d129471 q = 1) : d13990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d129471 q = 1) : d13991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d129471 q = 1) : d14065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d129471 q = 1) : d14119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d14119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d14119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39466 (p : Pattern) (ha : d381 p = 1) (hb : d129471 p = 1) : d14124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d129471 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39444 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d129471 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d129471 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d129471 q = 1) : d13990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d129471 q = 1) : d14071 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d129471 q = 1) : d14072 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d129471 q = 1) : d14124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d14124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d14124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39467 (p : Pattern) (ha : d5355 p = 1) (hb : d129471 p = 1) : d14133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d129471 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39444 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d129471 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d129471 q = 1) : d14109 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d129471 q = 1) : d14110 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d129471 q = 1) : d14111 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d129471 q = 1) : d14133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d14133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d14133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39468 (p : Pattern) (ha : d15985 p = 1) (hb : d129471 p = 1) : d14128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d129471 q = 1) : d14086 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39462 q ha hb
    | true =>
      simp only [d15973, d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d129471 q = 1) : d14087 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d129471 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39444 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d129471 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d129471 q = 1) : d14088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d129471 q = 1) : d14089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d129471 q = 1) : d14090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d129471 q = 1) : d14128 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d14128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d14128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39469 (p : Pattern) (ha : d128200 p = 1) (hb : d129471 p = 1) : d125460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d129471 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d129471 q = 1) : d14067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39458 q ha hb
    | true =>
      simp only [d297, d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d129471 q = 1) : d14068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d129471 q = 1) : d14069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d129471 q = 1) : d14070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d129471 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d129471 q = 1) : d14074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39459 q ha hb
    | true =>
      simp only [d304, d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d129471 q = 1) : d14075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d129471 q = 1) : d14076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d129471 q = 1) : d14092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39463 q ha hb
    | true =>
      simp only [d15979, d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39451 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d129471 q = 1) : d125451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d129471 q = 1) : d14113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39460 q ha hb
    | true =>
      simp only [d4737, d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d129471 q = 1) : d14114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d129471 q = 1) : d125452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d129471 q = 1) : d125453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d129471 q = 1) : d125454 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d129471 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d129471 q = 1) : d14120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d14120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39465 q ha hb
    | true =>
      simp only [d377, d14120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d129471 q = 1) : d14121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d14121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d14121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d129471 q = 1) : d14122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d14122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d14122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d129471 q = 1) : d14123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d14123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d14123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d129471 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d129471 q = 1) : d14125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d14125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39466 q ha hb
    | true =>
      simp only [d382, d14125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d129471 q = 1) : d14126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d14126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d14126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d129471 q = 1) : d14127 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d14127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d14127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d15986 q = 1) (hb : d129471 q = 1) : d14129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39468 q ha hb
    | true =>
      simp only [d15986, d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39445 q ha hb
  have h27 (q : Pattern) (ha : d128196 q = 1) (hb : d129471 q = 1) : d125456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d128196, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d129471 q = 1) : d14134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39467 q ha hb
    | true =>
      simp only [d5356, d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d129471 q = 1) : d14135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d128197 q = 1) (hb : d129471 q = 1) : d125457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d128197, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d128198 q = 1) (hb : d129471 q = 1) : d125458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, d125458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d128198, d125458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d128199 q = 1) (hb : d129471 q = 1) : d125459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, d125459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128199, d125459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d128200 q = 1) (hb : d129471 q = 1) : d125460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, d125460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128200, d125460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro39470 (p : Pattern) (ha : d128207 p = 1) (hb : d129471 p = 1) : d125467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d129471 q = 1) : d14129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39468 q ha hb
    | true =>
      simp only [d15986, d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39445 q ha hb
  have h2 (q : Pattern) (ha : d128196 q = 1) (hb : d129471 q = 1) : d125456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d129471 q = 1) : d14134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39467 q ha hb
    | true =>
      simp only [d5356, d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d129471 q = 1) : d14135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128197 q = 1) (hb : d129471 q = 1) : d125457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128205 q = 1) (hb : d129471 q = 1) : d125465 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d125465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, d125465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128206 q = 1) (hb : d129471 q = 1) : d125466 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d125466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, d125466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d129471 q = 1) : d125467 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d125467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d125467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39471 (p : Pattern) (ha : d5377 p = 1) (hb : d129471 p = 1) : d14189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d129471 q = 1) : d14027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39448 q ha hb
    | true =>
      simp only [d238, d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d129471 q = 1) : d14028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d129471 q = 1) : d14186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d14186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d14186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d129471 q = 1) : d14187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d14187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d14187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d129471 q = 1) : d14188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d14188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d14188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d129471 q = 1) : d14189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d14189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d14189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39472 (p : Pattern) (ha : d16004 p = 1) (hb : d129471 p = 1) : d14156 p = 1 := by
  have h0 (q : Pattern) (ha : d415 q = 1) (hb : d100904 q = 1) : d415 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d229 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d416 q = 1) (hb : d129471 q = 1) : d14154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d129471, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d416, d129471, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12602 q = 1) (hb : d100904 q = 1) : d12602 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12603 q = 1) (hb : d129471 q = 1) : d14155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d129471, d14155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12603, d129471, d14155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16004 q = 1) (hb : d129471 q = 1) : d14156 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d14156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16004, d14156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39473 (p : Pattern) (ha : d16010 p = 1) (hb : d129471 p = 1) : d14162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d129471 q = 1) : d14157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39472 q ha hb
    | true =>
      simp only [d16005, d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39447 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d129471 q = 1) : d14158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d129471 q = 1) : d14159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d129471 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d129471 q = 1) : d14021 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39447 q ha hb
    | true =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d129471 q = 1) : d14022 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d129471 q = 1) : d14023 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d129471 q = 1) : d14160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d129471 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d235 q = 1) (hb : d129471 q = 1) : d14024 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16009 q = 1) (hb : d129471 q = 1) : d14161 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d14161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16009, d14161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16010 q = 1) (hb : d129471 q = 1) : d14162 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d14162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16010, d14162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro39474 (p : Pattern) (ha : d16016 p = 1) (hb : d129471 p = 1) : d14168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d129471 q = 1) : d14163 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d14163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39473 q ha hb
    | true =>
      simp only [d16011, d14163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d129471 q = 1) : d14164 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d14164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d14164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d129471 q = 1) : d14027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39448 q ha hb
    | true =>
      simp only [d238, d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d129471 q = 1) : d14028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d129471 q = 1) : d14165 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d14165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d14165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d129471 q = 1) : d14166 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d14166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d14166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d129471 q = 1) : d14167 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d14167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d14167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d129471 q = 1) : d14168 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d14168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d14168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39475 (p : Pattern) (ha : d128217 p = 1) (hb : d129471 p = 1) : d125477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d129471 q = 1) : d14169 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d14169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39474 q ha hb
    | true =>
      simp only [d16017, d14169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39449 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d129471 q = 1) : d125473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d125473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, d125473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d129471 q = 1) : d14190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d14190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39471 q ha hb
    | true =>
      simp only [d5378, d14190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d129471 q = 1) : d14191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d14191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d14191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d129471 q = 1) : d125474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d125474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d125474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d129471 q = 1) : d125475 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d125475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d125475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d129471 q = 1) : d125476 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d125476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d125476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d129471 q = 1) : d125477 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d125477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d125477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39476 (p : Pattern) (ha : d128223 p = 1) (hb : d129471 p = 1) : d125483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d129471 q = 1) : d14055 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d14055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d14055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39455 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d129471 q = 1) : d14056 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d14056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d14056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d129471 q = 1) : d14062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39455 q ha hb
    | true =>
      simp only [d292, d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39456 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d129471 q = 1) : d14063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d129471 q = 1) : d14064 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d14064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d14064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128201 q = 1) (hb : d129471 q = 1) : d125461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, d125461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39464 q ha hb
    | true =>
      simp only [d128201, d125461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39469 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d129471 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d129471 q = 1) : d14142 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d14142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39457 q ha hb
    | true =>
      simp only [d398, d14142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128202 q = 1) (hb : d129471 q = 1) : d125462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, d125462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, d125462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128203 q = 1) (hb : d129471 q = 1) : d125463 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d125463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128203, d125463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d128204 q = 1) (hb : d129471 q = 1) : d125464 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d125464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128204, d125464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128208 q = 1) (hb : d129471 q = 1) : d125468 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d125468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128208, d125468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39470 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d129471 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d128209 q = 1) (hb : d129471 q = 1) : d125469 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d125469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128209, d125469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128210 q = 1) (hb : d129471 q = 1) : d125470 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d125470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128210, d125470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128211 q = 1) (hb : d129471 q = 1) : d125471 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d125471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128211, d125471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d128212 q = 1) (hb : d129471 q = 1) : d125472 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d125472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128212, d125472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128218 q = 1) (hb : d129471 q = 1) : d125478 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d125478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128218, d125478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39475 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d129471 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d128219 q = 1) (hb : d129471 q = 1) : d125479 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d125479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128219, d125479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d128220 q = 1) (hb : d129471 q = 1) : d125480 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d125480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128220, d125480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128221 q = 1) (hb : d129471 q = 1) : d125481 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d125481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128221, d125481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128222 q = 1) (hb : d129471 q = 1) : d125482 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d125482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128222, d125482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d128223 q = 1) (hb : d129471 q = 1) : d125483 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d125483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128223, d125483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro39477 (p : Pattern) (ha : d128229 p = 1) (hb : d129471 p = 1) : d125489 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d129471 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d129471 q = 1) : d125446 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39454 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d129471 q = 1) : d125447 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d129471 q = 1) : d125448 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d129471 q = 1) : d125449 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d129471 q = 1) : d125450 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d129471 q = 1) : d125484 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d125484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d125484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39476 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d129471 q = 1) : d125485 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d125485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d125485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d129471 q = 1) : d125486 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d125486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d125486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d129471 q = 1) : d125487 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d125487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d125487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d129471 q = 1) : d125488 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d125488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d125488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d129471 q = 1) : d125489 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d125489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d125489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39478 (p : Pattern) (ha : d481 p = 1) (hb : d129471 p = 1) : d14214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d129471 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d129471 q = 1) : d13982 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39443 q ha hb
    | true =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d129471 q = 1) : d13983 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d129471 q = 1) : d13984 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d129471 q = 1) : d14208 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d129471 q = 1) : d14213 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d14213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d14213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d129471 q = 1) : d14214 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d14214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d14214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39479 (p : Pattern) (ha : d491 p = 1) (hb : d129471 p = 1) : d14224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d129471 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39478 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d129471 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d129471 q = 1) : d14221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d129471 q = 1) : d14222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d129471 q = 1) : d14223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d129471 q = 1) : d14224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d14224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d14224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39480 (p : Pattern) (ha : d501 p = 1) (hb : d129471 p = 1) : d14234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d129471 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39478 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d129471 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d129471 q = 1) : d14221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d129471 q = 1) : d14222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d129471 q = 1) : d14223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d129471 q = 1) : d14234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d14234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d14234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39481 (p : Pattern) (ha : d644 p = 1) (hb : d129471 p = 1) : d14355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d129471 q = 1) : d14344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39479 q ha hb
    | true =>
      simp only [d633, d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d129471 q = 1) : d14345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d129471 q = 1) : d14346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d129471 q = 1) : d14347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d129471 q = 1) : d14348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d129471 q = 1) : d14350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39480 q ha hb
    | true =>
      simp only [d639, d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d129471 q = 1) : d14351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d129471 q = 1) : d14352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d129471 q = 1) : d14353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d129471 q = 1) : d14354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d129471 q = 1) : d14355 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d14355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d14355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39482 (p : Pattern) (ha : d653 p = 1) (hb : d129471 p = 1) : d14364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d129471 q = 1) : d14350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39480 q ha hb
    | true =>
      simp only [d639, d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d129471 q = 1) : d14351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d129471 q = 1) : d14352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d129471 q = 1) : d14353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d129471 q = 1) : d14354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d129471 q = 1) : d14364 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d14364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d14364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39483 (p : Pattern) (ha : d683 p = 1) (hb : d129471 p = 1) : d14395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d129471 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d129471 q = 1) : d14021 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39447 q ha hb
    | true =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d129471 q = 1) : d14022 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d129471 q = 1) : d14023 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d129471 q = 1) : d14385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d129471 q = 1) : d14394 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d14394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, d14394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d129471 q = 1) : d14395 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d14395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d14395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39484 (p : Pattern) (ha : d730 p = 1) (hb : d129471 p = 1) : d14447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d129471 q = 1) : d14396 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39483 q ha hb
    | true =>
      simp only [d684, d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d129471 q = 1) : d14397 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d129471 q = 1) : d14444 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d14444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d14444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d129471 q = 1) : d14445 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d14445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d14445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d129471 q = 1) : d14446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d14446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d14446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d129471 q = 1) : d14447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d14447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d14447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39485 (p : Pattern) (ha : d736 p = 1) (hb : d129471 p = 1) : d14453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d129471 q = 1) : d14448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d14448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39484 q ha hb
    | true =>
      simp only [d731, d14448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d129471 q = 1) : d14449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d14449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d14449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d129471 q = 1) : d14450 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d14450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d14450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d129471 q = 1) : d14451 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d14451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d14451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d129471 q = 1) : d14452 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d14452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d14452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d129471 q = 1) : d14453 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d14453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d14453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39486 (p : Pattern) (ha : d16036 p = 1) (hb : d129471 p = 1) : d14210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d129471 q = 1) : d14080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39461 q ha hb
    | true =>
      simp only [d15967, d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39443 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d129471 q = 1) : d14081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d129471 q = 1) : d14082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d129471 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d129471 q = 1) : d13982 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39443 q ha hb
    | true =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d129471 q = 1) : d13983 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d129471 q = 1) : d13984 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d129471 q = 1) : d14083 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d129471 q = 1) : d14208 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16035 q = 1) (hb : d129471 q = 1) : d14209 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d14209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16035, d14209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16036 q = 1) (hb : d129471 q = 1) : d14210 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d14210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16036, d14210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro39487 (p : Pattern) (ha : d16042 p = 1) (hb : d129471 p = 1) : d14220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d129471 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39486 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d129471 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d129471 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39478 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d129471 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d129471 q = 1) : d14217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d129471 q = 1) : d14218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d129471 q = 1) : d14219 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d129471 q = 1) : d14220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, d14220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, d14220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39488 (p : Pattern) (ha : d16048 p = 1) (hb : d129471 p = 1) : d14230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d129471 q = 1) : d14225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39487 q ha hb
    | true =>
      simp only [d16043, d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39479 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d129471 q = 1) : d14226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d129471 q = 1) : d14227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d129471 q = 1) : d14228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d129471 q = 1) : d14229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d129471 q = 1) : d14230 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, d14230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, d14230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39489 (p : Pattern) (ha : d16051 p = 1) (hb : d129471 p = 1) : d14233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d129471 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39486 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d129471 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d129471 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39478 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d129471 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d129471 q = 1) : d14217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d129471 q = 1) : d14218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d129471 q = 1) : d14219 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d129471 q = 1) : d14233 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d14233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d14233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39490 (p : Pattern) (ha : d16057 p = 1) (hb : d129471 p = 1) : d14240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d129471 q = 1) : d14225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39487 q ha hb
    | true =>
      simp only [d16043, d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39479 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d129471 q = 1) : d14226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d129471 q = 1) : d14227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d129471 q = 1) : d14228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d129471 q = 1) : d14229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16052 q = 1) (hb : d129471 q = 1) : d14235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39489 q ha hb
    | true =>
      simp only [d16052, d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39480 q ha hb
  have h7 (q : Pattern) (ha : d16053 q = 1) (hb : d129471 q = 1) : d14236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16054 q = 1) (hb : d129471 q = 1) : d14237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16054, d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16055 q = 1) (hb : d129471 q = 1) : d14238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16056 q = 1) (hb : d129471 q = 1) : d14239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16057 q = 1) (hb : d129471 q = 1) : d14240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16057, d14240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16057, d14240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39491 (p : Pattern) (ha : d16143 p = 1) (hb : d129471 p = 1) : d14349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d129471 q = 1) : d14225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39487 q ha hb
    | true =>
      simp only [d16043, d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39479 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d129471 q = 1) : d14226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d129471 q = 1) : d14227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d129471 q = 1) : d14228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d129471 q = 1) : d14229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d129471 q = 1) : d14344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39479 q ha hb
    | true =>
      simp only [d633, d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d129471 q = 1) : d14345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d129471 q = 1) : d14346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d129471 q = 1) : d14347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d129471 q = 1) : d14348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16143 q = 1) (hb : d129471 q = 1) : d14349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16143, d14349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16143, d14349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39492 (p : Pattern) (ha : d514 p = 1) (hb : d129471 p = 1) : d14247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d129471 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39478 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d129471 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d129471 q = 1) : d14221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d129471 q = 1) : d14222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d129471 q = 1) : d14246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d129471 q = 1) : d14247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d14247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d14247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39493 (p : Pattern) (ha : d524 p = 1) (hb : d129471 p = 1) : d14257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d129471 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39478 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d129471 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d129471 q = 1) : d14221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d129471 q = 1) : d14255 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d129471 q = 1) : d14256 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d129471 q = 1) : d14257 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d14257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d14257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39494 (p : Pattern) (ha : d16062 p = 1) (hb : d129471 p = 1) : d14245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d129471 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39486 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d129471 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d129471 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39478 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d129471 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d129471 q = 1) : d14217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d129471 q = 1) : d14218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d129471 q = 1) : d14244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16062 q = 1) (hb : d129471 q = 1) : d14245 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16062, d14245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16062, d14245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39495 (p : Pattern) (ha : d16069 p = 1) (hb : d129471 p = 1) : d14254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d129471 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39486 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d129471 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d129471 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39478 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d129471 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d129471 q = 1) : d14217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d129471 q = 1) : d14252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d129471 q = 1) : d14253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16069 q = 1) (hb : d129471 q = 1) : d14254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16069, d14254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16069, d14254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39496 (p : Pattern) (ha : d16077 p = 1) (hb : d129471 p = 1) : d14263 p = 1 := by
  have h0 (q : Pattern) (ha : d546 q = 1) (hb : d100904 q = 1) : d546 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16074 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16075 q = 1) (hb : d129471 q = 1) : d14261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d129471, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16075, d129471, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12749 q = 1) (hb : d100904 q = 1) : d12749 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12494 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16076 q = 1) (hb : d129471 q = 1) : d14262 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16076, d129471, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16076, d129471, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16077 q = 1) (hb : d129471 q = 1) : d14263 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16077, d14263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16077, d14263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39497 (p : Pattern) (ha : d16081 p = 1) (hb : d129471 p = 1) : d14267 p = 1 := by
  have h0 (q : Pattern) (ha : d12494 q = 1) (hb : d100904 q = 1) : d12494 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12495 q = 1) (hb : d129471 q = 1) : d14078 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d129471, d14078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12495, d129471, d14078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d29 q = 1) (hb : d129471 q = 1) : d29 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16081 q = 1) (hb : d129471 q = 1) : d14267 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d14267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16081, d14267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39498 (p : Pattern) (ha : d16087 p = 1) (hb : d129471 p = 1) : d14273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16078 q = 1) (hb : d129471 q = 1) : d14264 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, d14264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39496 q ha hb
    | true =>
      simp only [d16078, d14264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39461 q ha hb
  have h2 (q : Pattern) (ha : d16079 q = 1) (hb : d129471 q = 1) : d14265 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16079, d14265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16079, d14265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16080 q = 1) (hb : d129471 q = 1) : d14266 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16080, d14266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16080, d14266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d129471 q = 1) : d14268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d14268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39461 q ha hb
    | true =>
      simp only [d16082, d14268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39497 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d129471 q = 1) : d14269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d14269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d14269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d129471 q = 1) : d14270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d14270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d14270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16085 q = 1) (hb : d129471 q = 1) : d14271 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16085, d14271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16085, d14271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d129471 q = 1) : d14080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39461 q ha hb
    | true =>
      simp only [d15967, d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39443 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d129471 q = 1) : d14081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d129471 q = 1) : d14082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d129471 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d145 q = 1) (hb : d129471 q = 1) : d13982 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39443 q ha hb
    | true =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146 q = 1) (hb : d129471 q = 1) : d13983 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147 q = 1) (hb : d129471 q = 1) : d13984 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15970 q = 1) (hb : d129471 q = 1) : d14083 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16086 q = 1) (hb : d129471 q = 1) : d14272 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16086, d14272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16086, d14272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16087 q = 1) (hb : d129471 q = 1) : d14273 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16087, d14273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16087, d14273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro39499 (p : Pattern) (ha : d16093 p = 1) (hb : d129471 p = 1) : d14279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d129471 q = 1) : d14274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39498 q ha hb
    | true =>
      simp only [d16088, d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d129471 q = 1) : d14275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d129471 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39486 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d129471 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d129471 q = 1) : d14276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d129471 q = 1) : d14277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d129471 q = 1) : d14278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16093 q = 1) (hb : d129471 q = 1) : d14279 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16093, d14279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16093, d14279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
