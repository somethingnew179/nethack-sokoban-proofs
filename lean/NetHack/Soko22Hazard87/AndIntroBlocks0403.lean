import NetHack.Soko22Hazard87.AndIntroBlocks0402
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro100750 (p : Pattern) (ha : d365053 p = 1) (hb : d365286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365048 q = 1) (hb : d365281 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d365048, d365281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100749 q ha hb
    | true =>
      simp only [d365048, d365281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365049 q = 1) (hb : d365282 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d365049, d365282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365049, d365282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365050 q = 1) (hb : d365283 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d365050, d365283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365050, d365283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365051 q = 1) (hb : d365284 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d365051, d365284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365051, d365284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365052 q = 1) (hb : d365285 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d365052, d365285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365052, d365285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365053 q = 1) (hb : d365286 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d365053, d365286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365053, d365286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100751 (p : Pattern) (ha : d365059 p = 1) (hb : d365292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365054 q = 1) (hb : d365287 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d365054, d365287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100750 q ha hb
    | true =>
      simp only [d365054, d365287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365055 q = 1) (hb : d365288 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d365055, d365288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365055, d365288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365056 q = 1) (hb : d365289 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d365056, d365289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365056, d365289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365057 q = 1) (hb : d365290 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d365057, d365290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365057, d365290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365058 q = 1) (hb : d365291 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d365058, d365291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365058, d365291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365059 q = 1) (hb : d365292 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d365059, d365292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365059, d365292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100752 (p : Pattern) (ha : d308 p = 1) (hb : d357443 p = 1) : d365295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42565 q = 1) : d365091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42565, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100658 q ha hb
    | true =>
      simp only [d42565, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100659 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42566 q = 1) : d365092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42566, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42566, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42567 q = 1) : d365093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42567, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42567, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42568 q = 1) : d365094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42568, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42568, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42569 q = 1) : d365095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42569, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42569, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357443 q = 1) : d365295 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357443, d365295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357443, d365295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100753 (p : Pattern) (ha : d308 p = 1) (hb : d357454 p = 1) : d365306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d357449 q = 1) : d365301 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d357449, d365301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100693 q ha hb
    | true =>
      simp only [d357449, d365301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100667 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357450 q = 1) : d365302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357450, d365302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357450, d365302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357451 q = 1) : d365303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357451, d365303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357451, d365303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357452 q = 1) : d365304 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357452, d365304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357452, d365304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357453 q = 1) : d365305 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357453, d365305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357453, d365305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357454 q = 1) : d365306 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357454, d365306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357454, d365306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100754 (p : Pattern) (ha : d308 p = 1) (hb : d357460 p = 1) : d365312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42571 q = 1) : d365097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42571, d365097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100657 q ha hb
    | true =>
      simp only [d42571, d365097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100660 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42572 q = 1) : d365098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42572, d365098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42572, d365098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357441 q = 1) : d365293 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357441, d365293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357441, d365293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357442 q = 1) : d365294 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357442, d365294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357442, d365294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357444 q = 1) : d365296 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357444, d365296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357444, d365296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100752 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357445 q = 1) : d365297 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357445, d365297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357445, d365297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d357446 q = 1) : d365298 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357446, d365298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357446, d365298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d357447 q = 1) : d365299 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357447, d365299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357447, d365299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d357448 q = 1) : d365300 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357448, d365300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357448, d365300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d357455 q = 1) : d365307 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357455, d365307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357455, d365307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100753 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d357456 q = 1) : d365308 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357456, d365308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357456, d365308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d357457 q = 1) : d365309 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357457, d365309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357457, d365309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d357458 q = 1) : d365310 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357458, d365310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357458, d365310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d357459 q = 1) : d365311 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357459, d365311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357459, d365311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d357460 q = 1) : d365312 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357460, d365312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357460, d365312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100755 (p : Pattern) (ha : d308 p = 1) (hb : d357466 p = 1) : d365318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d357461 q = 1) : d365313 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357461, d365313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357461, d365313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100754 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357462 q = 1) : d365314 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357462, d365314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357462, d365314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357463 q = 1) : d365315 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357463, d365315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357463, d365315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357464 q = 1) : d365316 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357464, d365316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357464, d365316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357465 q = 1) : d365317 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357465, d365317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357465, d365317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357466 q = 1) : d365318 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357466, d365318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357466, d365318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100756 (p : Pattern) (ha : d357556 p = 1) (hb : d364959 p = 1) : d365324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d357440 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357467 q = 1) (hb : d364955 q = 1) : d365319 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357467, d364955, d365319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357467, d364955, d365319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100755 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d357494 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d357495 q = 1) (hb : d364956 q = 1) : d365320 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357495, d364956, d365320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357495, d364956, d365320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d357523 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d357524 q = 1) (hb : d364957 q = 1) : d365321 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357524, d364957, d365321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357524, d364957, d365321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d357553 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357554 q = 1) (hb : d364958 q = 1) : d365322 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d357554, d364958, d365322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357554, d364958, d365322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d357555 q = 1) (hb : d364959 q = 1) : d365323 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d364959, d365323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357555, d364959, d365323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d364959 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d357556 q = 1) (hb : d364959 q = 1) : d365324 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, d365324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357556, d365324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100757 (p : Pattern) (ha : d357562 p = 1) (hb : d364960 p = 1) : d365330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364959 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357557 q = 1) (hb : d364959 q = 1) : d365325 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, d365325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100756 q ha hb
    | true =>
      simp only [d357557, d365325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357558 q = 1) (hb : d364959 q = 1) : d365326 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, d365326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, d365326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357559 q = 1) (hb : d364959 q = 1) : d365327 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, d365327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357559, d365327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357560 q = 1) (hb : d364959 q = 1) : d365328 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d365328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357560, d365328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357561 q = 1) (hb : d364959 q = 1) : d365329 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d365329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357561, d365329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357562 q = 1) (hb : d364960 q = 1) : d365330 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d364960, d365330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357562, d364960, d365330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100758 (p : Pattern) (ha : d357568 p = 1) (hb : d364965 p = 1) : d365336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357563 q = 1) (hb : d364961 q = 1) : d365331 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d364961, d365331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100757 q ha hb
    | true =>
      simp only [d357563, d364961, d365331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357564 q = 1) (hb : d364962 q = 1) : d365332 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d364962, d365332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d364962, d365332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357565 q = 1) (hb : d364963 q = 1) : d365333 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d364963, d365333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357565, d364963, d365333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357566 q = 1) (hb : d364964 q = 1) : d365334 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d364964, d365334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357566, d364964, d365334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357567 q = 1) (hb : d364965 q = 1) : d365335 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d364965, d365335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357567, d364965, d365335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d364965 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357568 q = 1) (hb : d364965 q = 1) : d365336 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, d365336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357568, d365336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100759 (p : Pattern) (ha : d357574 p = 1) (hb : d364965 p = 1) : d365342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357569 q = 1) (hb : d364965 q = 1) : d365337 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, d365337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100758 q ha hb
    | true =>
      simp only [d357569, d365337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357570 q = 1) (hb : d364965 q = 1) : d365338 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, d365338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, d365338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357571 q = 1) (hb : d364965 q = 1) : d365339 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, d365339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, d365339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357572 q = 1) (hb : d364965 q = 1) : d365340 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, d365340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, d365340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357573 q = 1) (hb : d364965 q = 1) : d365341 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, d365341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, d365341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357574 q = 1) (hb : d364965 q = 1) : d365342 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, d365342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, d365342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100760 (p : Pattern) (ha : d357580 p = 1) (hb : d364965 p = 1) : d365348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357575 q = 1) (hb : d364965 q = 1) : d365343 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, d365343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100759 q ha hb
    | true =>
      simp only [d357575, d365343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357576 q = 1) (hb : d364965 q = 1) : d365344 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, d365344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, d365344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357577 q = 1) (hb : d364965 q = 1) : d365345 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, d365345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, d365345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357578 q = 1) (hb : d364965 q = 1) : d365346 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, d365346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, d365346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357579 q = 1) (hb : d364965 q = 1) : d365347 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, d365347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, d365347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357580 q = 1) (hb : d364965 q = 1) : d365348 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, d365348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, d365348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100761 (p : Pattern) (ha : d357586 p = 1) (hb : d364965 p = 1) : d365354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357581 q = 1) (hb : d364965 q = 1) : d365349 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, d365349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100760 q ha hb
    | true =>
      simp only [d357581, d365349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357582 q = 1) (hb : d364965 q = 1) : d365350 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, d365350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, d365350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357583 q = 1) (hb : d364965 q = 1) : d365351 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, d365351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, d365351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357584 q = 1) (hb : d364965 q = 1) : d365352 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, d365352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, d365352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357585 q = 1) (hb : d364965 q = 1) : d365353 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, d365353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, d365353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357586 q = 1) (hb : d364965 q = 1) : d365354 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, d365354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, d365354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100762 (p : Pattern) (ha : d357592 p = 1) (hb : d364965 p = 1) : d365360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357587 q = 1) (hb : d364965 q = 1) : d365355 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, d365355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100761 q ha hb
    | true =>
      simp only [d357587, d365355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357588 q = 1) (hb : d364965 q = 1) : d365356 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, d365356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, d365356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357589 q = 1) (hb : d364965 q = 1) : d365357 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, d365357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, d365357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357590 q = 1) (hb : d364965 q = 1) : d365358 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, d365358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, d365358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357591 q = 1) (hb : d364965 q = 1) : d365359 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, d365359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, d365359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357592 q = 1) (hb : d364965 q = 1) : d365360 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, d365360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, d365360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100763 (p : Pattern) (ha : d357598 p = 1) (hb : d364965 p = 1) : d365366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357593 q = 1) (hb : d364965 q = 1) : d365361 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, d365361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100762 q ha hb
    | true =>
      simp only [d357593, d365361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357594 q = 1) (hb : d364965 q = 1) : d365362 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, d365362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, d365362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357595 q = 1) (hb : d364965 q = 1) : d365363 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, d365363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, d365363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357596 q = 1) (hb : d364965 q = 1) : d365364 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, d365364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, d365364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357597 q = 1) (hb : d364965 q = 1) : d365365 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, d365365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, d365365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357598 q = 1) (hb : d364965 q = 1) : d365366 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, d365366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, d365366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100764 (p : Pattern) (ha : d361473 p = 1) (hb : d365086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361420 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361426 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d361462 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d361329 q = 1) (hb : d365081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100711 q ha hb
    | true =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
  have h5 (q : Pattern) (ha : d361463 q = 1) (hb : d365082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361463, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d361463, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d361469 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d361470 q = 1) (hb : d365083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361470, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361470, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d361471 q = 1) (hb : d365084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361471, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361471, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361472 q = 1) (hb : d365085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361472, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361472, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361473 q = 1) (hb : d365086 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361473, d365086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361473, d365086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100765 (p : Pattern) (ha : d361492 p = 1) (hb : d365096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361420 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361426 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361462 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361329 q = 1) (hb : d365081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100711 q ha hb
    | true =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
  have h4 (q : Pattern) (ha : d361463 q = 1) (hb : d365082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361463, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361463, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d361469 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d361470 q = 1) (hb : d365083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361470, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361470, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d361471 q = 1) (hb : d365084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361471, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361471, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361472 q = 1) (hb : d365085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361472, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361472, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d361478 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d361482 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d361484 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d361345 q = 1) (hb : d365091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361345, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100713 q ha hb
    | true =>
      simp only [d361345, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
  have h13 (q : Pattern) (ha : d361485 q = 1) (hb : d365092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361485, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d361485, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d361488 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d361489 q = 1) (hb : d365093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361489, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361489, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d361490 q = 1) (hb : d365094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361490, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d361490, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361491 q = 1) (hb : d365095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361491, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d361491, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d361492 q = 1) (hb : d365096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361492, d365096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361492, d365096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100766 (p : Pattern) (ha : d361501 p = 1) (hb : d365295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361484 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d361345 q = 1) (hb : d365091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361345, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100713 q ha hb
    | true =>
      simp only [d361345, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
  have h3 (q : Pattern) (ha : d361485 q = 1) (hb : d365092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361485, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361485, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d361488 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d361489 q = 1) (hb : d365093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361489, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361489, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d361499 q = 1) (hb : d365094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361499, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361499, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361500 q = 1) (hb : d365095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361500, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361500, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361501 q = 1) (hb : d365295 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361501, d365295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361501, d365295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100767 (p : Pattern) (ha : d361543 p = 1) (hb : d365306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361532 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d361383 q = 1) (hb : d365301 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361383, d365301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100735 q ha hb
    | true =>
      simp only [d361383, d365301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100740 q ha hb
  have h3 (q : Pattern) (ha : d361533 q = 1) (hb : d365302 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361533, d365302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361533, d365302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d361539 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d361540 q = 1) (hb : d365303 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361540, d365303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361540, d365303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d361541 q = 1) (hb : d365304 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361541, d365304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361541, d365304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361542 q = 1) (hb : d365305 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361542, d365305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361542, d365305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361543 q = 1) (hb : d365306 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361543, d365306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361543, d365306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100768 (p : Pattern) (ha : d361555 p = 1) (hb : d365312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361414 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361493 q = 1) (hb : d365097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361493, d365097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100764 q ha hb
    | true =>
      simp only [d361493, d365097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100765 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361495 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361496 q = 1) (hb : d365098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361496, d365098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361496, d365098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d361497 q = 1) (hb : d365293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361497, d365293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361497, d365293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d361498 q = 1) (hb : d365294 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361498, d365294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361498, d365294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361502 q = 1) (hb : d365296 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361502, d365296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d361502, d365296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100766 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d361504 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d361505 q = 1) (hb : d365297 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361505, d365297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361505, d365297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d361506 q = 1) (hb : d365298 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361506, d365298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361506, d365298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d361507 q = 1) (hb : d365299 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361507, d365299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361507, d365299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d361508 q = 1) (hb : d365300 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361508, d365300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361508, d365300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d361544 q = 1) (hb : d365307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361544, d365307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d361544, d365307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100767 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d361550 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d361551 q = 1) (hb : d365308 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361551, d365308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361551, d365308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d361552 q = 1) (hb : d365309 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361552, d365309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361552, d365309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d361553 q = 1) (hb : d365310 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361553, d365310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361553, d365310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d361554 q = 1) (hb : d365311 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361554, d365311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d361554, d365311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d361555 q = 1) (hb : d365312 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d361555, d365312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361555, d365312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100769 (p : Pattern) (ha : d361561 p = 1) (hb : d365318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361399 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d361556 q = 1) (hb : d365313 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d361556, d365313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361556, d365313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100768 q ha hb
  have h3 (q : Pattern) (ha : d361557 q = 1) (hb : d365314 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d361557, d365314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361557, d365314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361558 q = 1) (hb : d365315 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d361558, d365315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361558, d365315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361559 q = 1) (hb : d365316 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d361559, d365316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361559, d365316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361560 q = 1) (hb : d365317 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d361560, d365317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361560, d365317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361561 q = 1) (hb : d365318 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d361561, d365318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361561, d365318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100770 (p : Pattern) (ha : d365017 p = 1) (hb : d365324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361561 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361561 q = 1) (hb : d365319 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d365319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d365319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100769 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d365013 q = 1) (hb : d365320 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d365013, d365320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365013, d365320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d365014 q = 1) (hb : d365321 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d365014, d365321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365014, d365321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d365015 q = 1) (hb : d365322 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d365015, d365322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365015, d365322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d365016 q = 1) (hb : d365323 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d365016, d365323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365016, d365323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d365017 q = 1) (hb : d365324 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d365017, d365324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d365017, d365324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h7 p ha hb
theorem andIntro100771 (p : Pattern) (ha : d365023 p = 1) (hb : d365330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365018 q = 1) (hb : d365325 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d365018, d365325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100770 q ha hb
    | true =>
      simp only [d365018, d365325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365019 q = 1) (hb : d365326 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d365019, d365326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365019, d365326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365020 q = 1) (hb : d365327 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d365020, d365327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365020, d365327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365021 q = 1) (hb : d365328 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d365021, d365328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365021, d365328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365022 q = 1) (hb : d365329 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d365022, d365329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365022, d365329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365023 q = 1) (hb : d365330 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d365023, d365330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365023, d365330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100772 (p : Pattern) (ha : d365029 p = 1) (hb : d365336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365024 q = 1) (hb : d365331 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d365024, d365331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100771 q ha hb
    | true =>
      simp only [d365024, d365331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365025 q = 1) (hb : d365332 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d365025, d365332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365025, d365332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365026 q = 1) (hb : d365333 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d365026, d365333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365026, d365333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365027 q = 1) (hb : d365334 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d365027, d365334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365027, d365334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365028 q = 1) (hb : d365335 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d365028, d365335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365028, d365335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365029 q = 1) (hb : d365336 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d365029, d365336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365029, d365336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100773 (p : Pattern) (ha : d365035 p = 1) (hb : d365342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365030 q = 1) (hb : d365337 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d365030, d365337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100772 q ha hb
    | true =>
      simp only [d365030, d365337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365031 q = 1) (hb : d365338 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d365031, d365338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365031, d365338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365032 q = 1) (hb : d365339 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d365032, d365339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365032, d365339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365033 q = 1) (hb : d365340 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d365033, d365340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365033, d365340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365034 q = 1) (hb : d365341 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d365034, d365341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365034, d365341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365035 q = 1) (hb : d365342 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d365035, d365342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365035, d365342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100774 (p : Pattern) (ha : d365041 p = 1) (hb : d365348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365036 q = 1) (hb : d365343 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d365036, d365343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100773 q ha hb
    | true =>
      simp only [d365036, d365343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365037 q = 1) (hb : d365344 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d365037, d365344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365037, d365344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365038 q = 1) (hb : d365345 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d365038, d365345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365038, d365345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365039 q = 1) (hb : d365346 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d365039, d365346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365039, d365346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365040 q = 1) (hb : d365347 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d365040, d365347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365040, d365347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365041 q = 1) (hb : d365348 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d365041, d365348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365041, d365348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100775 (p : Pattern) (ha : d365047 p = 1) (hb : d365354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365042 q = 1) (hb : d365349 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d365042, d365349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100774 q ha hb
    | true =>
      simp only [d365042, d365349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365043 q = 1) (hb : d365350 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d365043, d365350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365043, d365350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365044 q = 1) (hb : d365351 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d365044, d365351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365044, d365351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365045 q = 1) (hb : d365352 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d365045, d365352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365045, d365352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365046 q = 1) (hb : d365353 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d365046, d365353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365046, d365353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365047 q = 1) (hb : d365354 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d365047, d365354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365047, d365354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100776 (p : Pattern) (ha : d365053 p = 1) (hb : d365360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365048 q = 1) (hb : d365355 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d365048, d365355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100775 q ha hb
    | true =>
      simp only [d365048, d365355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365049 q = 1) (hb : d365356 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d365049, d365356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365049, d365356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365050 q = 1) (hb : d365357 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d365050, d365357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365050, d365357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365051 q = 1) (hb : d365358 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d365051, d365358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365051, d365358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365052 q = 1) (hb : d365359 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d365052, d365359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365052, d365359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365053 q = 1) (hb : d365360 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d365053, d365360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365053, d365360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100777 (p : Pattern) (ha : d365059 p = 1) (hb : d365366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365054 q = 1) (hb : d365361 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d365054, d365361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100776 q ha hb
    | true =>
      simp only [d365054, d365361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365055 q = 1) (hb : d365362 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d365055, d365362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365055, d365362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365056 q = 1) (hb : d365363 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d365056, d365363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365056, d365363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365057 q = 1) (hb : d365364 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d365057, d365364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365057, d365364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365058 q = 1) (hb : d365365 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d365058, d365365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365058, d365365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365059 q = 1) (hb : d365366 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d365059, d365366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365059, d365366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100778 (p : Pattern) (ha : d362977 p = 1) (hb : d365086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359216 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d359222 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d359258 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d365081 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d362973 q = 1) (hb : d365082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362973, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d362973, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d359293 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d362974 q = 1) (hb : d365083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362974, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362974, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d362975 q = 1) (hb : d365084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362975, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362975, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d362976 q = 1) (hb : d365085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362976, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362976, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362977 q = 1) (hb : d365086 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362977, d365086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362977, d365086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100779 (p : Pattern) (ha : d362982 p = 1) (hb : d365096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d359216 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359222 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d359258 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d365081 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d362973 q = 1) (hb : d365082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362973, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362973, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d359293 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d362974 q = 1) (hb : d365083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362974, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362974, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d362975 q = 1) (hb : d365084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362975, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362975, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362976 q = 1) (hb : d365085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362976, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362976, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d359302 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d359306 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d359308 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d365091 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d362978 q = 1) (hb : d365092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362978, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d362978, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d359314 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d362979 q = 1) (hb : d365093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362979, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362979, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d362980 q = 1) (hb : d365094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362980, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d362980, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d362981 q = 1) (hb : d365095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362981, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d362981, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d362982 q = 1) (hb : d365096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362982, d365096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d362982, d365096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100780 (p : Pattern) (ha : d362989 p = 1) (hb : d365295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d365091 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362978 q = 1) (hb : d365092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362978, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362978, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d359314 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d362979 q = 1) (hb : d365093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362979, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362979, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d362987 q = 1) (hb : d365094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362987, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362987, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362988 q = 1) (hb : d365095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362988, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362988, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362989 q = 1) (hb : d365295 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362989, d365295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362989, d365295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100781 (p : Pattern) (ha : d362999 p = 1) (hb : d365306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359358 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d365301 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362995 q = 1) (hb : d365302 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362995, d365302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362995, d365302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d359384 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d362996 q = 1) (hb : d365303 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362996, d365303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362996, d365303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d362997 q = 1) (hb : d365304 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362997, d365304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362997, d365304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362998 q = 1) (hb : d365305 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362998, d365305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362998, d365305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362999 q = 1) (hb : d365306 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362999, d365306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362999, d365306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100782 (p : Pattern) (ha : d363005 p = 1) (hb : d365312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d359210 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362983 q = 1) (hb : d365097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362983, d365097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100778 q ha hb
    | true =>
      simp only [d362983, d365097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100779 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d359321 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362984 q = 1) (hb : d365098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362984, d365098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362984, d365098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d362985 q = 1) (hb : d365293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362985, d365293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362985, d365293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362986 q = 1) (hb : d365294 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362986, d365294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362986, d365294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362990 q = 1) (hb : d365296 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362990, d365296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362990, d365296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100780 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d359330 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d362991 q = 1) (hb : d365297 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362991, d365297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362991, d365297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d362992 q = 1) (hb : d365298 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362992, d365298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362992, d365298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d362993 q = 1) (hb : d365299 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362993, d365299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d362993, d365299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d362994 q = 1) (hb : d365300 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d362994, d365300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362994, d365300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d363000 q = 1) (hb : d365307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d363000, d365307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363000, d365307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100781 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d359395 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d363001 q = 1) (hb : d365308 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d363001, d365308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d363001, d365308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d363002 q = 1) (hb : d365309 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d363002, d365309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d363002, d365309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d363003 q = 1) (hb : d365310 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d363003, d365310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d363003, d365310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d363004 q = 1) (hb : d365311 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d363004, d365311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d363004, d365311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d363005 q = 1) (hb : d365312 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d363005, d365312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d363005, d365312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100783 (p : Pattern) (ha : d363011 p = 1) (hb : d365318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d363006 q = 1) (hb : d365313 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d363006, d365313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363006, d365313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100782 q ha hb
  have h3 (q : Pattern) (ha : d363007 q = 1) (hb : d365314 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d363007, d365314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363007, d365314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d363008 q = 1) (hb : d365315 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d363008, d365315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363008, d365315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d363009 q = 1) (hb : d365316 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d363009, d365316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363009, d365316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d363010 q = 1) (hb : d365317 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d363010, d365317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363010, d365317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363011 q = 1) (hb : d365318 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d363011, d365318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d363011, d365318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100784 (p : Pattern) (ha : d365324 p = 1) (hb : d365371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363011 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363011 q = 1) (hb : d365319 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d365319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d365319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100783 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d365320 q = 1) (hb : d365367 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d365320, d365367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d365320, d365367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d365321 q = 1) (hb : d365368 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d365321, d365368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365321, d365368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d365322 q = 1) (hb : d365369 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d365322, d365369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365322, d365369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d365323 q = 1) (hb : d365370 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d365323, d365370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365323, d365370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d365324 q = 1) (hb : d365371 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d365324, d365371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d365324, d365371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro100785 (p : Pattern) (ha : d365330 p = 1) (hb : d365377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365325 q = 1) (hb : d365372 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d365325, d365372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100784 q ha hb
    | true =>
      simp only [d365325, d365372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365326 q = 1) (hb : d365373 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d365326, d365373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365326, d365373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365327 q = 1) (hb : d365374 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d365327, d365374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365327, d365374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365328 q = 1) (hb : d365375 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d365328, d365375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365328, d365375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365329 q = 1) (hb : d365376 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d365329, d365376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365329, d365376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365330 q = 1) (hb : d365377 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d365330, d365377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365330, d365377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100786 (p : Pattern) (ha : d365336 p = 1) (hb : d365383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365331 q = 1) (hb : d365378 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d365331, d365378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100785 q ha hb
    | true =>
      simp only [d365331, d365378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365332 q = 1) (hb : d365379 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d365332, d365379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365332, d365379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365333 q = 1) (hb : d365380 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d365333, d365380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365333, d365380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365334 q = 1) (hb : d365381 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d365334, d365381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365334, d365381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365335 q = 1) (hb : d365382 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d365335, d365382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365335, d365382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365336 q = 1) (hb : d365383 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d365336, d365383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365336, d365383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100787 (p : Pattern) (ha : d365342 p = 1) (hb : d365389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365337 q = 1) (hb : d365384 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d365337, d365384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100786 q ha hb
    | true =>
      simp only [d365337, d365384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365338 q = 1) (hb : d365385 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d365338, d365385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365338, d365385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365339 q = 1) (hb : d365386 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d365339, d365386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365339, d365386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365340 q = 1) (hb : d365387 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d365340, d365387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365340, d365387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365341 q = 1) (hb : d365388 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d365341, d365388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365341, d365388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365342 q = 1) (hb : d365389 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d365342, d365389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365342, d365389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100788 (p : Pattern) (ha : d365348 p = 1) (hb : d365395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365343 q = 1) (hb : d365390 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d365343, d365390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100787 q ha hb
    | true =>
      simp only [d365343, d365390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365344 q = 1) (hb : d365391 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d365344, d365391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365344, d365391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365345 q = 1) (hb : d365392 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d365345, d365392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365345, d365392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365346 q = 1) (hb : d365393 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d365346, d365393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365346, d365393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365347 q = 1) (hb : d365394 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d365347, d365394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365347, d365394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365348 q = 1) (hb : d365395 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d365348, d365395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365348, d365395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100789 (p : Pattern) (ha : d365354 p = 1) (hb : d365401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365349 q = 1) (hb : d365396 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d365349, d365396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100788 q ha hb
    | true =>
      simp only [d365349, d365396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365350 q = 1) (hb : d365397 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d365350, d365397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365350, d365397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365351 q = 1) (hb : d365398 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d365351, d365398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365351, d365398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365352 q = 1) (hb : d365399 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d365352, d365399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365352, d365399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365353 q = 1) (hb : d365400 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d365353, d365400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365353, d365400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365354 q = 1) (hb : d365401 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d365354, d365401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365354, d365401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100790 (p : Pattern) (ha : d365360 p = 1) (hb : d365407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365355 q = 1) (hb : d365402 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d365355, d365402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100789 q ha hb
    | true =>
      simp only [d365355, d365402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365356 q = 1) (hb : d365403 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d365356, d365403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365356, d365403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365357 q = 1) (hb : d365404 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d365357, d365404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365357, d365404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365358 q = 1) (hb : d365405 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d365358, d365405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365358, d365405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365359 q = 1) (hb : d365406 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d365359, d365406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365359, d365406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365360 q = 1) (hb : d365407 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d365360, d365407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365360, d365407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100791 (p : Pattern) (ha : d365366 p = 1) (hb : d365413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365361 q = 1) (hb : d365408 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d365361, d365408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100790 q ha hb
    | true =>
      simp only [d365361, d365408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365362 q = 1) (hb : d365409 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d365362, d365409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365362, d365409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365363 q = 1) (hb : d365410 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d365363, d365410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365363, d365410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365364 q = 1) (hb : d365411 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d365364, d365411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365364, d365411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365365 q = 1) (hb : d365412 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d365365, d365412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365365, d365412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365366 q = 1) (hb : d365413 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d365366, d365413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365366, d365413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100792 (p : Pattern) (ha : d36 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100648 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100793 (p : Pattern) (ha : d42 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100792 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100794 (p : Pattern) (ha : d49 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100792 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100795 (p : Pattern) (ha : d111 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100794 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100796 (p : Pattern) (ha : d308 p = 1) (hb : d406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100794 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d406 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro100797 (p : Pattern) (ha : d77 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100664 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100798 (p : Pattern) (ha : d83 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100797 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100799 (p : Pattern) (ha : d308 p = 1) (hb : d462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100798 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d460 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d461 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d462 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100800 (p : Pattern) (ha : d308 p = 1) (hb : d42267 p = 1) : d365070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42262 q = 1) : d365060 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100650 q ha hb
    | true =>
      simp only [d42262, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100648 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42263 q = 1) : d365061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42263, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42264 q = 1) : d365062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42264, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100648 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42265 q = 1) : d365064 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42265, d365064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42265, d365064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42266 q = 1) : d365069 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42266, d365069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42266, d365069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42267 q = 1) : d365070 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42267, d365070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42267, d365070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100801 (p : Pattern) (ha : d308 p = 1) (hb : d42273 p = 1) : d365080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42268 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100800 q ha hb
    | true =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42269 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100792 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42270 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42271 q = 1) : d365078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42271, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42272 q = 1) : d365079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42272, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42272, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42273 q = 1) : d365080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42273, d365080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42273, d365080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100802 (p : Pattern) (ha : d308 p = 1) (hb : d42338 p = 1) : d365545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42274 q = 1) : d365159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100801 q ha hb
    | true =>
      simp only [d42274, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42334 q = 1) : d365160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42334, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42334, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42335 q = 1) : d365161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42335, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42335, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42336 q = 1) : d365162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42336, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42336, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42337 q = 1) : d365163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42337, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42337, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42338 q = 1) : d365545 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42338, d365545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42338, d365545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100803 (p : Pattern) (ha : d308 p = 1) (hb : d42280 p = 1) : d365090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42268 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100800 q ha hb
    | true =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42269 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100792 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42270 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42271 q = 1) : d365078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42271, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42272 q = 1) : d365079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42272, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42272, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42280 q = 1) : d365090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42280, d365090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42280, d365090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100804 (p : Pattern) (ha : d308 p = 1) (hb : d42345 p = 1) : d365170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42274 q = 1) : d365159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100801 q ha hb
    | true =>
      simp only [d42274, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42334 q = 1) : d365160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42334, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42334, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42335 q = 1) : d365161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42335, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42335, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42336 q = 1) : d365162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42336, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42336, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42337 q = 1) : d365163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42337, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42337, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42281 q = 1) : d365165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100803 q ha hb
    | true =>
      simp only [d42281, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100794 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42341 q = 1) : d365166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42341, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42341, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42342 q = 1) : d365167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42342, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42342, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42343 q = 1) : d365168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42343, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42343, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42344 q = 1) : d365169 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42344, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42344, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42345 q = 1) : d365170 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42345, d365170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42345, d365170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100805 (p : Pattern) (ha : d308 p = 1) (hb : d42459 p = 1) : d365578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42274 q = 1) : d365159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100801 q ha hb
    | true =>
      simp only [d42274, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42334 q = 1) : d365160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42334, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42334, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42335 q = 1) : d365161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42335, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42335, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42336 q = 1) : d365162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42336, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42336, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42337 q = 1) : d365163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42337, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42337, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42459 q = 1) : d365578 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42459, d365578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42459, d365578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro100806 (p : Pattern) (ha : d116 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100792 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100807 (p : Pattern) (ha : d123 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100792 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100808 (p : Pattern) (ha : d308 p = 1) (hb : d42350 p = 1) : d365103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42268 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100800 q ha hb
    | true =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42269 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100792 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42270 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42271 q = 1) : d365078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42271, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42349 q = 1) : d365102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42349, d365102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42349, d365102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42350 q = 1) : d365103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42350, d365103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42350, d365103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100809 (p : Pattern) (ha : d308 p = 1) (hb : d42357 p = 1) : d365113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42268 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100800 q ha hb
    | true =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42269 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100792 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42270 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42355 q = 1) : d365111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42355, d365111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42355, d365111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42356 q = 1) : d365112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42356, d365112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42356, d365112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42357 q = 1) : d365113 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42357, d365113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42357, d365113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100810 (p : Pattern) (ha : d308 p = 1) (hb : d42389 p = 1) : d365066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42384 q = 1) : d364541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42384, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100652 q ha hb
    | true =>
      simp only [d42384, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100650 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42385 q = 1) : d364542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42385, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42385, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42386 q = 1) : d364543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42386, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42386, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42262 q = 1) : d365060 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100650 q ha hb
    | true =>
      simp only [d42262, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100648 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42263 q = 1) : d365061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42263, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42264 q = 1) : d365062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42264, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42387 q = 1) : d365063 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42387, d365063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42387, d365063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100648 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42265 q = 1) : d365064 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42265, d365064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42265, d365064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42388 q = 1) : d365065 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42388, d365065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42388, d365065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42389 q = 1) : d365066 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42389, d365066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42389, d365066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro100811 (p : Pattern) (ha : d308 p = 1) (hb : d42395 p = 1) : d365076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42390 q = 1) : d365067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42390, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100810 q ha hb
    | true =>
      simp only [d42390, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42391 q = 1) : d365068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42391, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42391, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42268 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100800 q ha hb
    | true =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42269 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42392 q = 1) : d365073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42392, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42392, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42393 q = 1) : d365074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42393, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42393, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42394 q = 1) : d365075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42394, d365075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42394, d365075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42395 q = 1) : d365076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42395, d365076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42395, d365076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100812 (p : Pattern) (ha : d308 p = 1) (hb : d42430 p = 1) : d365080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42268 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100800 q ha hb
    | true =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42269 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42427 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42427, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42427, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42428 q = 1) : d365078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42428, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42428, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42429 q = 1) : d365079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42429, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42429, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42430 q = 1) : d365080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42430, d365080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42430, d365080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100813 (p : Pattern) (ha : d308 p = 1) (hb : d309809 p = 1) : d365563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42351 q = 1) : d365551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42351, d365551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100808 q ha hb
    | true =>
      simp only [d42351, d365551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100806 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42352 q = 1) : d365552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42352, d365552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42352, d365552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42353 q = 1) : d365553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42353, d365553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42353, d365553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42354 q = 1) : d365554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42354, d365554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42354, d365554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42358 q = 1) : d365555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42358, d365555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100809 q ha hb
    | true =>
      simp only [d42358, d365555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100807 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42359 q = 1) : d365556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42359, d365556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42359, d365556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42360 q = 1) : d365557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42360, d365557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42360, d365557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42396 q = 1) : d365081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42396, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100811 q ha hb
    | true =>
      simp only [d42396, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100801 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309805 q = 1) : d365558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d365558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309805, d365558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42431 q = 1) : d365159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42431, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100812 q ha hb
    | true =>
      simp only [d42431, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42432 q = 1) : d365559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42432, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42432, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309806 q = 1) : d365560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d365560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309806, d365560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309807 q = 1) : d365561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d365561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309807, d365561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309808 q = 1) : d365562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d365562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309808, d365562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d309809 q = 1) : d365563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309809, d365563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309809, d365563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100814 (p : Pattern) (ha : d194 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100792 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100815 (p : Pattern) (ha : d199 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100792 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100816 (p : Pattern) (ha : d308 p = 1) (hb : d42437 p = 1) : d365138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42268 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100800 q ha hb
    | true =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42269 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100792 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42270 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42271 q = 1) : d365078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42271, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42349 q = 1) : d365102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42349, d365102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42349, d365102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42437 q = 1) : d365138 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42437, d365138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42437, d365138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100817 (p : Pattern) (ha : d308 p = 1) (hb : d42442 p = 1) : d365144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42268 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100800 q ha hb
    | true =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42269 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100792 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42270 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42355 q = 1) : d365111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42355, d365111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42355, d365111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42356 q = 1) : d365112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42356, d365112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42356, d365112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42442 q = 1) : d365144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42442, d365144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42442, d365144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100818 (p : Pattern) (ha : d308 p = 1) (hb : d42446 p = 1) : d365089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42390 q = 1) : d365067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42390, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100810 q ha hb
    | true =>
      simp only [d42390, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42391 q = 1) : d365068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42391, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42391, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42268 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100800 q ha hb
    | true =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42269 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42392 q = 1) : d365073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42392, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42392, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42393 q = 1) : d365074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42393, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42393, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42394 q = 1) : d365075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42394, d365075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42394, d365075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42446 q = 1) : d365089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42446, d365089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42446, d365089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100819 (p : Pattern) (ha : d308 p = 1) (hb : d42451 p = 1) : d365090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42268 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100800 q ha hb
    | true =>
      simp only [d42268, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42269 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42269, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42427 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42427, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42427, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42428 q = 1) : d365078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42428, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42428, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42429 q = 1) : d365079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42429, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42429, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42451 q = 1) : d365090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42451, d365090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42451, d365090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100820 (p : Pattern) (ha : d308 p = 1) (hb : d309814 p = 1) : d365576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42351 q = 1) : d365551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42351, d365551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100808 q ha hb
    | true =>
      simp only [d42351, d365551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100806 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42352 q = 1) : d365552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42352, d365552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42352, d365552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42353 q = 1) : d365553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42353, d365553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42353, d365553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42354 q = 1) : d365554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42354, d365554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42354, d365554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42358 q = 1) : d365555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42358, d365555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100809 q ha hb
    | true =>
      simp only [d42358, d365555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100807 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42359 q = 1) : d365556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42359, d365556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42359, d365556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42360 q = 1) : d365557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42360, d365557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42360, d365557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42396 q = 1) : d365081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42396, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100811 q ha hb
    | true =>
      simp only [d42396, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100801 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309805 q = 1) : d365558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d365558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309805, d365558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42431 q = 1) : d365159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42431, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100812 q ha hb
    | true =>
      simp only [d42431, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42432 q = 1) : d365559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42432, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42432, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309806 q = 1) : d365560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d365560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309806, d365560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309807 q = 1) : d365561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d365561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309807, d365561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309808 q = 1) : d365562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d365562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309808, d365562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42438 q = 1) : d365564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42438, d365564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100816 q ha hb
    | true =>
      simp only [d42438, d365564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100814 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42439 q = 1) : d365565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42439, d365565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42439, d365565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42440 q = 1) : d365566 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42440, d365566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42440, d365566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42441 q = 1) : d365567 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42441, d365567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42441, d365567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d42443 q = 1) : d365568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42443, d365568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100817 q ha hb
    | true =>
      simp only [d42443, d365568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100815 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d42444 q = 1) : d365569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42444, d365569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42444, d365569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d42445 q = 1) : d365570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42445, d365570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d42445, d365570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d42447 q = 1) : d365091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42447, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100818 q ha hb
    | true =>
      simp only [d42447, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100803 q ha hb
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d309810 q = 1) : d365571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d365571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309810, d365571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d308 q = 1) (hb : d42452 q = 1) : d365165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42452, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100819 q ha hb
    | true =>
      simp only [d42452, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h25 (q : Pattern) (ha : d308 q = 1) (hb : d42453 q = 1) : d365572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42453, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42453, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d309811 q = 1) : d365573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d365573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309811, d365573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d309812 q = 1) : d365574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309812, d365574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309812, d365574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d308 q = 1) (hb : d309813 q = 1) : d365575 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309813, d365575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309813, d365575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d308 q = 1) (hb : d309814 q = 1) : d365576 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309814, d365576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309814, d365576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro100821 (p : Pattern) (ha : d308 p = 1) (hb : d309821 p = 1) : d365585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42447 q = 1) : d365091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42447, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100818 q ha hb
    | true =>
      simp only [d42447, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100803 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309810 q = 1) : d365571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d365571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309810, d365571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42452 q = 1) : d365165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42452, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100819 q ha hb
    | true =>
      simp only [d42452, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42453 q = 1) : d365572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42453, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42453, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309811 q = 1) : d365573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d365573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309811, d365573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309819 q = 1) : d365583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309819, d365583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309819, d365583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d309820 q = 1) : d365584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309820, d365584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309820, d365584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309821 q = 1) : d365585 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309821, d365585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309821, d365585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100822 (p : Pattern) (ha : d308 p = 1) (hb : d42310 p = 1) : d365203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42305 q = 1) : d365185 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100665 q ha hb
    | true =>
      simp only [d42305, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100664 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42306 q = 1) : d365186 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42306, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42307 q = 1) : d365187 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42307, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100664 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42308 q = 1) : d365193 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42308, d365193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42308, d365193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42309 q = 1) : d365202 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42309, d365202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42309, d365202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42310 q = 1) : d365203 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42310, d365203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42310, d365203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100823 (p : Pattern) (ha : d308 p = 1) (hb : d42316 p = 1) : d365226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42311 q = 1) : d365204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42311, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100822 q ha hb
    | true =>
      simp only [d42311, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42312 q = 1) : d365205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42312, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42312, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100797 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42313 q = 1) : d365223 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42313, d365223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42313, d365223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42314 q = 1) : d365224 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42314, d365224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42314, d365224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42315 q = 1) : d365225 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42315, d365225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42315, d365225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42316 q = 1) : d365226 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42316, d365226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42316, d365226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100824 (p : Pattern) (ha : d308 p = 1) (hb : d42488 p = 1) : d365195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42483 q = 1) : d364708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42483, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100687 q ha hb
    | true =>
      simp only [d42483, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100665 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42484 q = 1) : d364709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42484, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42484, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42485 q = 1) : d364710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42485, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42485, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42305 q = 1) : d365185 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100665 q ha hb
    | true =>
      simp only [d42305, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100664 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42306 q = 1) : d365186 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42306, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42307 q = 1) : d365187 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42307, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42486 q = 1) : d365188 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42486, d365188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42486, d365188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100664 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42308 q = 1) : d365193 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42308, d365193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42308, d365193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42487 q = 1) : d365194 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42487, d365194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42487, d365194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42488 q = 1) : d365195 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42488, d365195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42488, d365195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro100825 (p : Pattern) (ha : d308 p = 1) (hb : d42494 p = 1) : d365209 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42489 q = 1) : d365196 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42489, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100824 q ha hb
    | true =>
      simp only [d42489, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42490 q = 1) : d365197 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42490, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42490, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42311 q = 1) : d365204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42311, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100822 q ha hb
    | true =>
      simp only [d42311, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42312 q = 1) : d365205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42312, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42312, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42491 q = 1) : d365206 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42491, d365206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42491, d365206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42492 q = 1) : d365207 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42492, d365207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42492, d365207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42493 q = 1) : d365208 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42493, d365208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42493, d365208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42494 q = 1) : d365209 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42494, d365209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42494, d365209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100826 (p : Pattern) (ha : d308 p = 1) (hb : d42519 p = 1) : d365226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42311 q = 1) : d365204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42311, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100822 q ha hb
    | true =>
      simp only [d42311, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42312 q = 1) : d365205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42312, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42312, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42516 q = 1) : d365223 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42516, d365223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42516, d365223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42517 q = 1) : d365224 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42517, d365224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42517, d365224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42518 q = 1) : d365225 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42518, d365225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42518, d365225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42519 q = 1) : d365226 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42519, d365226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42519, d365226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100827 (p : Pattern) (ha : d308 p = 1) (hb : d309831 p = 1) : d365596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42495 q = 1) : d365301 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42495, d365301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100825 q ha hb
    | true =>
      simp only [d42495, d365301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100823 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309827 q = 1) : d365591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309827, d365591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309827, d365591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42520 q = 1) : d365227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42520, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100826 q ha hb
    | true =>
      simp only [d42520, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42521 q = 1) : d365592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42521, d365592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42521, d365592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309828 q = 1) : d365593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309828, d365593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309828, d365593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309829 q = 1) : d365594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309829, d365594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309829, d365594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d309830 q = 1) : d365595 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309830, d365595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309830, d365595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309831 q = 1) : d365596 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309831, d365596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309831, d365596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100828 (p : Pattern) (ha : d308 p = 1) (hb : d309837 p = 1) : d365602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42339 q = 1) : d365546 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42339, d365546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42339, d365546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100802 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42340 q = 1) : d365547 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42340, d365547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42340, d365547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42346 q = 1) : d365548 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42346, d365548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100802 q ha hb
    | true =>
      simp only [d42346, d365548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100804 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42347 q = 1) : d365549 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42347, d365549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42347, d365549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42348 q = 1) : d365550 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d42348, d365550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42348, d365550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309815 q = 1) : d365577 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309815, d365577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100813 q ha hb
    | true =>
      simp only [d309815, d365577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100820 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42460 q = 1) : d365579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42460, d365579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100805 q ha hb
    | true =>
      simp only [d42460, d365579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100795 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309816 q = 1) : d365580 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309816, d365580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309816, d365580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309817 q = 1) : d365581 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309817, d365581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309817, d365581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d309818 q = 1) : d365582 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309818, d365582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309818, d365582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d309822 q = 1) : d365586 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309822, d365586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309822, d365586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100821 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100796 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309823 q = 1) : d365587 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309823, d365587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309823, d365587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309824 q = 1) : d365588 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309824, d365588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309824, d365588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d309825 q = 1) : d365589 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309825, d365589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309825, d365589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d309826 q = 1) : d365590 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309826, d365590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309826, d365590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d309832 q = 1) : d365597 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309832, d365597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309832, d365597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100827 q ha hb
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100799 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d309833 q = 1) : d365598 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309833, d365598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309833, d365598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d309834 q = 1) : d365599 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309834, d365599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309834, d365599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d309835 q = 1) : d365600 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309835, d365600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309835, d365600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d309836 q = 1) : d365601 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309836, d365601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309836, d365601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d309837 q = 1) : d365602 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309837, d365602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309837, d365602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro100829 (p : Pattern) (ha : d309843 p = 1) (hb : d365436 p = 1) : d365608 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d309804 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309838 q = 1) : d365603 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309838, d365603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309838, d365603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100828 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d309839 q = 1) : d365604 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309839, d365604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309839, d365604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d309840 q = 1) : d365605 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309840, d365605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309840, d365605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309841 q = 1) : d365606 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309841, d365606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309841, d365606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309842 q = 1) : d365607 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309842, d365607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309842, d365607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309843 q = 1) (hb : d365436 q = 1) : d365608 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d365436, d365608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309843, d365436, d365608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro100830 (p : Pattern) (ha : d310011 p = 1) (hb : d365441 p = 1) : d365614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d309882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309883 q = 1) (hb : d365437 q = 1) : d365609 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309883, d365437, d365609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100829 q ha hb
    | true =>
      simp only [d309883, d365437, d365609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309923 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309924 q = 1) (hb : d365438 q = 1) : d365610 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309924, d365438, d365610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309924, d365438, d365610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d309965 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309966 q = 1) (hb : d365439 q = 1) : d365611 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d365439, d365611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309966, d365439, d365611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d310008 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310009 q = 1) (hb : d365440 q = 1) : d365612 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d365440, d365612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310009, d365440, d365612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d310010 q = 1) (hb : d365441 q = 1) : d365613 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d365441, d365613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d310010, d365441, d365613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d365441 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d310011 q = 1) (hb : d365441 q = 1) : d365614 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, d365614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d310011, d365614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100831 (p : Pattern) (ha : d310017 p = 1) (hb : d365443 p = 1) : d365620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365441 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d365441 q = 1) : d365615 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, d365615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100830 q ha hb
    | true =>
      simp only [d310012, d365615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d365441 q = 1) : d365616 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d365616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d365616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310014 q = 1) (hb : d365441 q = 1) : d365617 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d365617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d365617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310015 q = 1) (hb : d365441 q = 1) : d365618 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d365618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310015, d365618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d310016 q = 1) (hb : d365442 q = 1) : d365619 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d365442, d365619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310016, d365442, d365619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d310017 q = 1) (hb : d365443 q = 1) : d365620 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d365443, d365620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d310017, d365443, d365620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro100832 (p : Pattern) (ha : d310023 p = 1) (hb : d365448 p = 1) : d365626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d365444 q = 1) : d365621 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d365444, d365621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100831 q ha hb
    | true =>
      simp only [d310018, d365444, d365621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d365445 q = 1) : d365622 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d365445, d365622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d365445, d365622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310020 q = 1) (hb : d365446 q = 1) : d365623 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d365446, d365623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d365446, d365623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310021 q = 1) (hb : d365447 q = 1) : d365624 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d365447, d365624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310021, d365447, d365624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310022 q = 1) (hb : d365448 q = 1) : d365625 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d365448, d365625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310022, d365448, d365625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d365448 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310023 q = 1) (hb : d365448 q = 1) : d365626 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, d365626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310023, d365626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100833 (p : Pattern) (ha : d310029 p = 1) (hb : d365448 p = 1) : d365632 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365448 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d365448 q = 1) : d365627 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, d365627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100832 q ha hb
    | true =>
      simp only [d310024, d365627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d365448 q = 1) : d365628 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, d365628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, d365628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d365448 q = 1) : d365629 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, d365629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, d365629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d365448 q = 1) : d365630 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, d365630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, d365630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d365448 q = 1) : d365631 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, d365631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, d365631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d365448 q = 1) : d365632 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, d365632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, d365632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100834 (p : Pattern) (ha : d310035 p = 1) (hb : d365448 p = 1) : d365638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365448 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d365448 q = 1) : d365633 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, d365633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100833 q ha hb
    | true =>
      simp only [d310030, d365633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d365448 q = 1) : d365634 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, d365634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, d365634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d365448 q = 1) : d365635 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, d365635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, d365635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d365448 q = 1) : d365636 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, d365636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, d365636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d365448 q = 1) : d365637 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, d365637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, d365637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d365448 q = 1) : d365638 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, d365638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, d365638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100835 (p : Pattern) (ha : d310041 p = 1) (hb : d365448 p = 1) : d365644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365448 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d365448 q = 1) : d365639 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, d365639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100834 q ha hb
    | true =>
      simp only [d310036, d365639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d365448 q = 1) : d365640 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, d365640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, d365640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d365448 q = 1) : d365641 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, d365641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, d365641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d365448 q = 1) : d365642 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, d365642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, d365642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d365448 q = 1) : d365643 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, d365643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, d365643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d365448 q = 1) : d365644 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, d365644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, d365644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100836 (p : Pattern) (ha : d310047 p = 1) (hb : d365448 p = 1) : d365650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365448 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d365448 q = 1) : d365645 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, d365645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100835 q ha hb
    | true =>
      simp only [d310042, d365645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d365448 q = 1) : d365646 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, d365646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, d365646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d365448 q = 1) : d365647 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, d365647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, d365647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d365448 q = 1) : d365648 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, d365648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, d365648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d365448 q = 1) : d365649 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, d365649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, d365649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d365448 q = 1) : d365650 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, d365650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, d365650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100837 (p : Pattern) (ha : d310053 p = 1) (hb : d365448 p = 1) : d365656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365448 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d365448 q = 1) : d365651 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, d365651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100836 q ha hb
    | true =>
      simp only [d310048, d365651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d365448 q = 1) : d365652 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, d365652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, d365652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d365448 q = 1) : d365653 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, d365653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, d365653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d365448 q = 1) : d365654 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, d365654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, d365654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d365448 q = 1) : d365655 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, d365655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, d365655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d365448 q = 1) : d365656 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, d365656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, d365656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100838 (p : Pattern) (ha : d361279 p = 1) (hb : d365545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361218 q = 1) (hb : d365159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
    | true =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361275 q = 1) (hb : d365160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361275, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361275, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361276 q = 1) (hb : d365161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361276, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361276, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361277 q = 1) (hb : d365162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361277, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361277, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361278 q = 1) (hb : d365163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361278, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361278, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361279 q = 1) (hb : d365545 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361279, d365545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361279, d365545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100839 (p : Pattern) (ha : d361334 p = 1) (hb : d365563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361292 q = 1) (hb : d365551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361292, d365551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100715 q ha hb
    | true =>
      simp only [d361292, d365551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361293 q = 1) (hb : d365552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361293, d365552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361293, d365552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361294 q = 1) (hb : d365553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361294, d365553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361294, d365553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361295 q = 1) (hb : d365554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361295, d365554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361295, d365554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361299 q = 1) (hb : d365555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361299, d365555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100716 q ha hb
    | true =>
      simp only [d361299, d365555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361300 q = 1) (hb : d365556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361300, d365556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361300, d365556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361301 q = 1) (hb : d365557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361301, d365557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361301, d365557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361329 q = 1) (hb : d365081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100711 q ha hb
    | true =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d361218 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d361330 q = 1) (hb : d365558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361330, d365558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361330, d365558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d361218 q = 1) (hb : d365159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
    | true =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361219 q = 1) (hb : d365559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361219, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361219, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361331 q = 1) (hb : d365560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361331, d365560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361331, d365560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361332 q = 1) (hb : d365561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361332, d365561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361332, d365561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d361333 q = 1) (hb : d365562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361333, d365562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361333, d365562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361334 q = 1) (hb : d365563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361334, d365563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361334, d365563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro100840 (p : Pattern) (ha : d361350 p = 1) (hb : d365576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361292 q = 1) (hb : d365551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361292, d365551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100715 q ha hb
    | true =>
      simp only [d361292, d365551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361293 q = 1) (hb : d365552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361293, d365552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361293, d365552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361294 q = 1) (hb : d365553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361294, d365553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361294, d365553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361295 q = 1) (hb : d365554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361295, d365554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361295, d365554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361299 q = 1) (hb : d365555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361299, d365555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100716 q ha hb
    | true =>
      simp only [d361299, d365555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361300 q = 1) (hb : d365556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361300, d365556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361300, d365556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361301 q = 1) (hb : d365557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361301, d365557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361301, d365557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361329 q = 1) (hb : d365081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100711 q ha hb
    | true =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d361218 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d361330 q = 1) (hb : d365558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361330, d365558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361330, d365558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d361218 q = 1) (hb : d365159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
    | true =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361219 q = 1) (hb : d365559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361219, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361219, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361331 q = 1) (hb : d365560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361331, d365560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361331, d365560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361332 q = 1) (hb : d365561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361332, d365561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361332, d365561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d361333 q = 1) (hb : d365562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361333, d365562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361333, d365562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361336 q = 1) (hb : d365564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361336, d365564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100723 q ha hb
    | true =>
      simp only [d361336, d365564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d361337 q = 1) (hb : d365565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361337, d365565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361337, d365565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d361338 q = 1) (hb : d365566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361338, d365566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d361338, d365566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d361339 q = 1) (hb : d365567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361339, d365567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361339, d365567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d361341 q = 1) (hb : d365568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361341, d365568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100724 q ha hb
    | true =>
      simp only [d361341, d365568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d361342 q = 1) (hb : d365569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361342, d365569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361342, d365569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d361343 q = 1) (hb : d365570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361343, d365570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d361343, d365570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d361345 q = 1) (hb : d365091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361345, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100713 q ha hb
    | true =>
      simp only [d361345, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d361225 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d361346 q = 1) (hb : d365571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361346, d365571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d361346, d365571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d361225 q = 1) (hb : d365165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
    | true =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d361226 q = 1) (hb : d365572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361226, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d361226, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d361347 q = 1) (hb : d365573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361347, d365573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d361347, d365573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d361348 q = 1) (hb : d365574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361348, d365574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d361348, d365574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d361349 q = 1) (hb : d365575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361349, d365575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d361349, d365575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d361350 q = 1) (hb : d365576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361350, d365576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361350, d365576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro100841 (p : Pattern) (ha : d361352 p = 1) (hb : d365578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361218 q = 1) (hb : d365159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
    | true =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361275 q = 1) (hb : d365160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361275, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361275, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361276 q = 1) (hb : d365161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361276, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361276, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361277 q = 1) (hb : d365162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361277, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361277, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361278 q = 1) (hb : d365163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361278, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361278, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361352 q = 1) (hb : d365578 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361352, d365578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361352, d365578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100842 (p : Pattern) (ha : d361359 p = 1) (hb : d365585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361345 q = 1) (hb : d365091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361345, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100713 q ha hb
    | true =>
      simp only [d361345, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361225 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361346 q = 1) (hb : d365571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361346, d365571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361346, d365571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d361225 q = 1) (hb : d365165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
    | true =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361226 q = 1) (hb : d365572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361226, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361226, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361347 q = 1) (hb : d365573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361347, d365573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361347, d365573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361357 q = 1) (hb : d365583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361357, d365583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361357, d365583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361358 q = 1) (hb : d365584 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361358, d365584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361358, d365584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361359 q = 1) (hb : d365585 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361359, d365585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361359, d365585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100843 (p : Pattern) (ha : d361388 p = 1) (hb : d365596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361383 q = 1) (hb : d365301 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361383, d365301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100735 q ha hb
    | true =>
      simp only [d361383, d365301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100740 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361259 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361384 q = 1) (hb : d365591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361384, d365591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361384, d365591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d361259 q = 1) (hb : d365227 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361259, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100740 q ha hb
    | true =>
      simp only [d361259, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361260 q = 1) (hb : d365592 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361260, d365592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361260, d365592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361385 q = 1) (hb : d365593 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361385, d365593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361385, d365593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361386 q = 1) (hb : d365594 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361386, d365594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361386, d365594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361387 q = 1) (hb : d365595 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361387, d365595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361387, d365595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361388 q = 1) (hb : d365596 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361388, d365596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361388, d365596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100844 (p : Pattern) (ha : d361394 p = 1) (hb : d365602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361280 q = 1) (hb : d365546 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361280, d365546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361280, d365546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100838 q ha hb
  have h2 (q : Pattern) (ha : d361281 q = 1) (hb : d365547 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361281, d365547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361281, d365547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361287 q = 1) (hb : d365548 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361287, d365548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100838 q ha hb
    | true =>
      simp only [d361287, d365548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100709 q ha hb
  have h4 (q : Pattern) (ha : d361288 q = 1) (hb : d365549 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361288, d365549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361288, d365549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361289 q = 1) (hb : d365550 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361289, d365550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361289, d365550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361351 q = 1) (hb : d365577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361351, d365577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100839 q ha hb
    | true =>
      simp only [d361351, d365577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100840 q ha hb
  have h7 (q : Pattern) (ha : d361353 q = 1) (hb : d365579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361353, d365579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100841 q ha hb
    | true =>
      simp only [d361353, d365579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361354 q = 1) (hb : d365580 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361354, d365580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361354, d365580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361355 q = 1) (hb : d365581 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361355, d365581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361355, d365581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d361356 q = 1) (hb : d365582 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361356, d365582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361356, d365582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361360 q = 1) (hb : d365586 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361360, d365586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361360, d365586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100842 q ha hb
  have h12 (q : Pattern) (ha : d361361 q = 1) (hb : d365587 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361361, d365587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361361, d365587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361362 q = 1) (hb : d365588 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361362, d365588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361362, d365588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d361363 q = 1) (hb : d365589 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361363, d365589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361363, d365589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d361364 q = 1) (hb : d365590 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361364, d365590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361364, d365590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361389 q = 1) (hb : d365597 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361389, d365597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361389, d365597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100843 q ha hb
  have h17 (q : Pattern) (ha : d361390 q = 1) (hb : d365598 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361390, d365598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361390, d365598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d361391 q = 1) (hb : d365599 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361391, d365599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d361391, d365599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d361392 q = 1) (hb : d365600 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361392, d365600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d361392, d365600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d361393 q = 1) (hb : d365601 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361393, d365601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d361393, d365601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d361394 q = 1) (hb : d365602 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d361394, d365602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361394, d365602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro100845 (p : Pattern) (ha : d361399 p = 1) (hb : d365608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361399 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361395 q = 1) (hb : d365603 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d361395, d365603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361395, d365603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100844 q ha hb
  have h4 (q : Pattern) (ha : d361396 q = 1) (hb : d365604 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d361396, d365604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361396, d365604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361397 q = 1) (hb : d365605 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d361397, d365605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361397, d365605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361398 q = 1) (hb : d365606 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d361398, d365606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361398, d365606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361399 q = 1) (hb : d365607 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d361399, d365607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361399, d365607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361399 q = 1) (hb : d365608 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d365608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d365608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100846 (p : Pattern) (ha : d365502 p = 1) (hb : d365614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365497 q = 1) (hb : d365609 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d365497, d365609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100845 q ha hb
    | true =>
      simp only [d365497, d365609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365498 q = 1) (hb : d365610 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d365498, d365610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365498, d365610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365499 q = 1) (hb : d365611 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d365499, d365611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365499, d365611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365500 q = 1) (hb : d365612 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d365500, d365612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365500, d365612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365501 q = 1) (hb : d365613 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d365501, d365613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365501, d365613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365502 q = 1) (hb : d365614 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d365502, d365614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365502, d365614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100847 (p : Pattern) (ha : d365508 p = 1) (hb : d365620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365503 q = 1) (hb : d365615 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d365503, d365615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100846 q ha hb
    | true =>
      simp only [d365503, d365615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365504 q = 1) (hb : d365616 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d365504, d365616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365504, d365616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365505 q = 1) (hb : d365617 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d365505, d365617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365505, d365617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365506 q = 1) (hb : d365618 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d365506, d365618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365506, d365618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365507 q = 1) (hb : d365619 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d365507, d365619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365507, d365619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365508 q = 1) (hb : d365620 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d365508, d365620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365508, d365620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100848 (p : Pattern) (ha : d365514 p = 1) (hb : d365626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365509 q = 1) (hb : d365621 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d365509, d365621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100847 q ha hb
    | true =>
      simp only [d365509, d365621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365510 q = 1) (hb : d365622 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d365510, d365622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365510, d365622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365511 q = 1) (hb : d365623 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d365511, d365623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365511, d365623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365512 q = 1) (hb : d365624 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d365512, d365624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365512, d365624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365513 q = 1) (hb : d365625 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d365513, d365625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365513, d365625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365514 q = 1) (hb : d365626 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d365514, d365626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365514, d365626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100849 (p : Pattern) (ha : d365520 p = 1) (hb : d365632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365515 q = 1) (hb : d365627 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d365515, d365627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100848 q ha hb
    | true =>
      simp only [d365515, d365627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365516 q = 1) (hb : d365628 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d365516, d365628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365516, d365628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365517 q = 1) (hb : d365629 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d365517, d365629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365517, d365629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365518 q = 1) (hb : d365630 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d365518, d365630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365518, d365630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365519 q = 1) (hb : d365631 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d365519, d365631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365519, d365631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365520 q = 1) (hb : d365632 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d365520, d365632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365520, d365632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100850 (p : Pattern) (ha : d365526 p = 1) (hb : d365638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365521 q = 1) (hb : d365633 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d365521, d365633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100849 q ha hb
    | true =>
      simp only [d365521, d365633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365522 q = 1) (hb : d365634 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d365522, d365634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365522, d365634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365523 q = 1) (hb : d365635 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d365523, d365635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365523, d365635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365524 q = 1) (hb : d365636 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d365524, d365636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365524, d365636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365525 q = 1) (hb : d365637 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d365525, d365637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365525, d365637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365526 q = 1) (hb : d365638 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d365526, d365638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365526, d365638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100851 (p : Pattern) (ha : d365532 p = 1) (hb : d365644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365527 q = 1) (hb : d365639 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d365527, d365639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100850 q ha hb
    | true =>
      simp only [d365527, d365639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365528 q = 1) (hb : d365640 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d365528, d365640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365528, d365640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365529 q = 1) (hb : d365641 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d365529, d365641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365529, d365641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365530 q = 1) (hb : d365642 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d365530, d365642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365530, d365642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365531 q = 1) (hb : d365643 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d365531, d365643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365531, d365643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365532 q = 1) (hb : d365644 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d365532, d365644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365532, d365644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100852 (p : Pattern) (ha : d365538 p = 1) (hb : d365650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365533 q = 1) (hb : d365645 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d365533, d365645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100851 q ha hb
    | true =>
      simp only [d365533, d365645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365534 q = 1) (hb : d365646 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d365534, d365646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365534, d365646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365535 q = 1) (hb : d365647 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d365535, d365647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365535, d365647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365536 q = 1) (hb : d365648 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d365536, d365648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365536, d365648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365537 q = 1) (hb : d365649 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d365537, d365649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365537, d365649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365538 q = 1) (hb : d365650 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d365538, d365650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365538, d365650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100853 (p : Pattern) (ha : d365544 p = 1) (hb : d365656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365539 q = 1) (hb : d365651 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d365539, d365651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100852 q ha hb
    | true =>
      simp only [d365539, d365651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365540 q = 1) (hb : d365652 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d365540, d365652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365540, d365652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365541 q = 1) (hb : d365653 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d365541, d365653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365541, d365653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365542 q = 1) (hb : d365654 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d365542, d365654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365542, d365654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365543 q = 1) (hb : d365655 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d365543, d365655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365543, d365655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365544 q = 1) (hb : d365656 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d365544, d365656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365544, d365656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100854 (p : Pattern) (ha : d308 p = 1) (hb : d357418 p = 1) : d365179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42281 q = 1) : d365165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100803 q ha hb
    | true =>
      simp only [d42281, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100794 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42341 q = 1) : d365166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42341, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42341, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42342 q = 1) : d365167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42342, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42342, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42343 q = 1) : d365168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42343, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42343, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42344 q = 1) : d365169 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42344, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42344, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357418 q = 1) : d365179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357418, d365179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357418, d365179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100855 (p : Pattern) (ha : d308 p = 1) (hb : d357428 p = 1) : d365232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42317 q = 1) : d365227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42317, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100823 q ha hb
    | true =>
      simp only [d42317, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100798 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357424 q = 1) : d365228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357424, d365228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357424, d365228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357425 q = 1) : d365229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357425, d365229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357425, d365229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357426 q = 1) : d365230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357426, d365230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357426, d365230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357427 q = 1) : d365231 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357427, d365231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357427, d365231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357428 q = 1) : d365232 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357428, d365232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357428, d365232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100856 (p : Pattern) (ha : d308 p = 1) (hb : d357434 p = 1) : d365667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42346 q = 1) : d365548 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42346, d365548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100802 q ha hb
    | true =>
      simp only [d42346, d365548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100804 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42347 q = 1) : d365549 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42347, d365549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42347, d365549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357416 q = 1) : d365657 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357416, d365657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357416, d365657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357417 q = 1) : d365658 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357417, d365658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357417, d365658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357419 q = 1) : d365180 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357419, d365180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357419, d365180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100854 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357420 q = 1) : d365659 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357420, d365659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357420, d365659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d357421 q = 1) : d365660 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357421, d365660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357421, d365660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d357422 q = 1) : d365661 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357422, d365661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357422, d365661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d357423 q = 1) : d365662 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357423, d365662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357423, d365662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d357429 q = 1) : d365233 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357429, d365233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357429, d365233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100855 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d357430 q = 1) : d365663 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357430, d365663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357430, d365663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d357431 q = 1) : d365664 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357431, d365664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357431, d365664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d357432 q = 1) : d365665 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357432, d365665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357432, d365665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d357433 q = 1) : d365666 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357433, d365666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357433, d365666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d357434 q = 1) : d365667 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357434, d365667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357434, d365667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100857 (p : Pattern) (ha : d357440 p = 1) (hb : d365436 p = 1) : d365673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357435 q = 1) : d365668 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357435, d365668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357435, d365668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100856 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357436 q = 1) : d365669 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357436, d365669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357436, d365669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357437 q = 1) : d365670 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357437, d365670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357437, d365670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357438 q = 1) : d365671 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357438, d365671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357438, d365671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357439 q = 1) : d365672 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357439, d365672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357439, d365672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d357440 q = 1) (hb : d365436 q = 1) : d365673 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357440, d365436, d365673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357440, d365436, d365673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro100858 (p : Pattern) (ha : d357556 p = 1) (hb : d365441 p = 1) : d365679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d357466 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357467 q = 1) (hb : d365437 q = 1) : d365674 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357467, d365437, d365674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100857 q ha hb
    | true =>
      simp only [d357467, d365437, d365674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d357494 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d357495 q = 1) (hb : d365438 q = 1) : d365675 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357495, d365438, d365675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357495, d365438, d365675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d357523 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d357524 q = 1) (hb : d365439 q = 1) : d365676 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357524, d365439, d365676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357524, d365439, d365676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d357553 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357554 q = 1) (hb : d365440 q = 1) : d365677 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d357554, d365440, d365677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357554, d365440, d365677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d357555 q = 1) (hb : d365441 q = 1) : d365678 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d365441, d365678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357555, d365441, d365678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d365441 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d357556 q = 1) (hb : d365441 q = 1) : d365679 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, d365679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357556, d365679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100859 (p : Pattern) (ha : d357562 p = 1) (hb : d365443 p = 1) : d365685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365441 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357557 q = 1) (hb : d365441 q = 1) : d365680 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, d365680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100858 q ha hb
    | true =>
      simp only [d357557, d365680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357558 q = 1) (hb : d365441 q = 1) : d365681 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, d365681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, d365681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357559 q = 1) (hb : d365441 q = 1) : d365682 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, d365682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357559, d365682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357560 q = 1) (hb : d365441 q = 1) : d365683 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d365683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357560, d365683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d357561 q = 1) (hb : d365442 q = 1) : d365684 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d365442, d365684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357561, d365442, d365684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d357562 q = 1) (hb : d365443 q = 1) : d365685 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d365443, d365685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357562, d365443, d365685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro100860 (p : Pattern) (ha : d357568 p = 1) (hb : d365448 p = 1) : d365691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357563 q = 1) (hb : d365444 q = 1) : d365686 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d365444, d365686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100859 q ha hb
    | true =>
      simp only [d357563, d365444, d365686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357564 q = 1) (hb : d365445 q = 1) : d365687 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d365445, d365687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d365445, d365687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357565 q = 1) (hb : d365446 q = 1) : d365688 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d365446, d365688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357565, d365446, d365688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357566 q = 1) (hb : d365447 q = 1) : d365689 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d365447, d365689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357566, d365447, d365689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357567 q = 1) (hb : d365448 q = 1) : d365690 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d365448, d365690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357567, d365448, d365690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d365448 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357568 q = 1) (hb : d365448 q = 1) : d365691 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, d365691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357568, d365691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100861 (p : Pattern) (ha : d357574 p = 1) (hb : d365448 p = 1) : d365697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365448 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357569 q = 1) (hb : d365448 q = 1) : d365692 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, d365692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100860 q ha hb
    | true =>
      simp only [d357569, d365692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357570 q = 1) (hb : d365448 q = 1) : d365693 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, d365693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, d365693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357571 q = 1) (hb : d365448 q = 1) : d365694 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, d365694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, d365694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357572 q = 1) (hb : d365448 q = 1) : d365695 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, d365695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, d365695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357573 q = 1) (hb : d365448 q = 1) : d365696 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, d365696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, d365696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357574 q = 1) (hb : d365448 q = 1) : d365697 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, d365697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, d365697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100862 (p : Pattern) (ha : d357580 p = 1) (hb : d365448 p = 1) : d365703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365448 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357575 q = 1) (hb : d365448 q = 1) : d365698 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, d365698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100861 q ha hb
    | true =>
      simp only [d357575, d365698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357576 q = 1) (hb : d365448 q = 1) : d365699 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, d365699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, d365699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357577 q = 1) (hb : d365448 q = 1) : d365700 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, d365700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, d365700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357578 q = 1) (hb : d365448 q = 1) : d365701 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, d365701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, d365701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357579 q = 1) (hb : d365448 q = 1) : d365702 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, d365702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, d365702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357580 q = 1) (hb : d365448 q = 1) : d365703 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, d365703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, d365703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100863 (p : Pattern) (ha : d357586 p = 1) (hb : d365448 p = 1) : d365709 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365448 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357581 q = 1) (hb : d365448 q = 1) : d365704 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, d365704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100862 q ha hb
    | true =>
      simp only [d357581, d365704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357582 q = 1) (hb : d365448 q = 1) : d365705 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, d365705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, d365705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357583 q = 1) (hb : d365448 q = 1) : d365706 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, d365706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, d365706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357584 q = 1) (hb : d365448 q = 1) : d365707 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, d365707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, d365707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357585 q = 1) (hb : d365448 q = 1) : d365708 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, d365708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, d365708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357586 q = 1) (hb : d365448 q = 1) : d365709 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, d365709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, d365709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100864 (p : Pattern) (ha : d357592 p = 1) (hb : d365448 p = 1) : d365715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365448 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357587 q = 1) (hb : d365448 q = 1) : d365710 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, d365710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100863 q ha hb
    | true =>
      simp only [d357587, d365710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357588 q = 1) (hb : d365448 q = 1) : d365711 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, d365711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, d365711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357589 q = 1) (hb : d365448 q = 1) : d365712 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, d365712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, d365712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357590 q = 1) (hb : d365448 q = 1) : d365713 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, d365713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, d365713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357591 q = 1) (hb : d365448 q = 1) : d365714 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, d365714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, d365714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357592 q = 1) (hb : d365448 q = 1) : d365715 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, d365715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, d365715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100865 (p : Pattern) (ha : d357598 p = 1) (hb : d365448 p = 1) : d365721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365448 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357593 q = 1) (hb : d365448 q = 1) : d365716 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, d365716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100864 q ha hb
    | true =>
      simp only [d357593, d365716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357594 q = 1) (hb : d365448 q = 1) : d365717 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, d365717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, d365717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357595 q = 1) (hb : d365448 q = 1) : d365718 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, d365718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, d365718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357596 q = 1) (hb : d365448 q = 1) : d365719 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, d365719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, d365719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357597 q = 1) (hb : d365448 q = 1) : d365720 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, d365720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, d365720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357598 q = 1) (hb : d365448 q = 1) : d365721 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, d365721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, d365721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100866 (p : Pattern) (ha : d361334 p = 1) (hb : d365545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361301 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d361329 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d361218 q = 1) (hb : d365159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
    | true =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361330 q = 1) (hb : d365160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361330, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d361330, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d361219 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d361331 q = 1) (hb : d365161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361331, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361331, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d361332 q = 1) (hb : d365162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361332, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361332, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361333 q = 1) (hb : d365163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361333, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361333, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361334 q = 1) (hb : d365545 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361334, d365545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361334, d365545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100867 (p : Pattern) (ha : d361350 p = 1) (hb : d365170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361295 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361301 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361329 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d361218 q = 1) (hb : d365159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
    | true =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d361330 q = 1) (hb : d365160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361330, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361330, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d361219 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d361331 q = 1) (hb : d365161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361331, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361331, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d361332 q = 1) (hb : d365162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361332, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361332, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361333 q = 1) (hb : d365163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361333, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361333, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d361339 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d361343 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d361345 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d361225 q = 1) (hb : d365165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
    | true =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d361346 q = 1) (hb : d365166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361346, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d361346, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d361226 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d361347 q = 1) (hb : d365167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361347, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d361347, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d361348 q = 1) (hb : d365168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361348, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d361348, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d361349 q = 1) (hb : d365169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361349, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d361349, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d361350 q = 1) (hb : d365170 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361350, d365170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361350, d365170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100868 (p : Pattern) (ha : d361359 p = 1) (hb : d365179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361345 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d361225 q = 1) (hb : d365165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
    | true =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361346 q = 1) (hb : d365166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361346, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361346, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d361226 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d361347 q = 1) (hb : d365167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361347, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361347, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d361357 q = 1) (hb : d365168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361357, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361357, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361358 q = 1) (hb : d365169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361358, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361358, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361359 q = 1) (hb : d365179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361359, d365179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361359, d365179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100869 (p : Pattern) (ha : d361388 p = 1) (hb : d365232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361383 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d361259 q = 1) (hb : d365227 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361259, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100740 q ha hb
    | true =>
      simp only [d361259, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361384 q = 1) (hb : d365228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361384, d365228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361384, d365228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d361260 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d361385 q = 1) (hb : d365229 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361385, d365229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361385, d365229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d361386 q = 1) (hb : d365230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361386, d365230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361386, d365230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361387 q = 1) (hb : d365231 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361387, d365231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361387, d365231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361388 q = 1) (hb : d365232 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361388, d365232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361388, d365232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100870 (p : Pattern) (ha : d361394 p = 1) (hb : d365667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361289 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361351 q = 1) (hb : d365548 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361351, d365548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100866 q ha hb
    | true =>
      simp only [d361351, d365548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100867 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361353 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361354 q = 1) (hb : d365549 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361354, d365549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361354, d365549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d361355 q = 1) (hb : d365657 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361355, d365657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361355, d365657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d361356 q = 1) (hb : d365658 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361356, d365658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361356, d365658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361360 q = 1) (hb : d365180 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361360, d365180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d361360, d365180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100868 q ha hb
  have h8 (q : Pattern) (ha : d361361 q = 1) (hb : d365659 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361361, d365659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361361, d365659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d361362 q = 1) (hb : d365660 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361362, d365660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361362, d365660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d361363 q = 1) (hb : d365661 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361363, d365661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361363, d365661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d361364 q = 1) (hb : d365662 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361364, d365662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361364, d365662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d361389 q = 1) (hb : d365233 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361389, d365233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d361389, d365233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100869 q ha hb
  have h13 (q : Pattern) (ha : d361390 q = 1) (hb : d365663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361390, d365663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361390, d365663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d361391 q = 1) (hb : d365664 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361391, d365664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361391, d365664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d361392 q = 1) (hb : d365665 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361392, d365665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d361392, d365665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d361393 q = 1) (hb : d365666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361393, d365666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361393, d365666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d361394 q = 1) (hb : d365667 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d361394, d365667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361394, d365667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro100871 (p : Pattern) (ha : d361399 p = 1) (hb : d365673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361399 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361395 q = 1) (hb : d365668 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d361395, d365668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361395, d365668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100870 q ha hb
  have h4 (q : Pattern) (ha : d361396 q = 1) (hb : d365669 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d361396, d365669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361396, d365669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361397 q = 1) (hb : d365670 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d361397, d365670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361397, d365670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361398 q = 1) (hb : d365671 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d361398, d365671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361398, d365671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361399 q = 1) (hb : d365672 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d361399, d365672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361399, d365672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361399 q = 1) (hb : d365673 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d365673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d365673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100872 (p : Pattern) (ha : d365502 p = 1) (hb : d365679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365497 q = 1) (hb : d365674 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d365497, d365674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100871 q ha hb
    | true =>
      simp only [d365497, d365674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365498 q = 1) (hb : d365675 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d365498, d365675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365498, d365675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365499 q = 1) (hb : d365676 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d365499, d365676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365499, d365676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365500 q = 1) (hb : d365677 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d365500, d365677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365500, d365677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365501 q = 1) (hb : d365678 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d365501, d365678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365501, d365678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365502 q = 1) (hb : d365679 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d365502, d365679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365502, d365679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100873 (p : Pattern) (ha : d365508 p = 1) (hb : d365685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365503 q = 1) (hb : d365680 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d365503, d365680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100872 q ha hb
    | true =>
      simp only [d365503, d365680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365504 q = 1) (hb : d365681 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d365504, d365681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365504, d365681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365505 q = 1) (hb : d365682 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d365505, d365682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365505, d365682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365506 q = 1) (hb : d365683 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d365506, d365683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365506, d365683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365507 q = 1) (hb : d365684 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d365507, d365684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365507, d365684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365508 q = 1) (hb : d365685 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d365508, d365685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365508, d365685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100874 (p : Pattern) (ha : d365514 p = 1) (hb : d365691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365509 q = 1) (hb : d365686 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d365509, d365686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100873 q ha hb
    | true =>
      simp only [d365509, d365686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365510 q = 1) (hb : d365687 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d365510, d365687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365510, d365687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365511 q = 1) (hb : d365688 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d365511, d365688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365511, d365688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365512 q = 1) (hb : d365689 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d365512, d365689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365512, d365689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365513 q = 1) (hb : d365690 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d365513, d365690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365513, d365690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365514 q = 1) (hb : d365691 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d365514, d365691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365514, d365691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100875 (p : Pattern) (ha : d365520 p = 1) (hb : d365697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365515 q = 1) (hb : d365692 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d365515, d365692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100874 q ha hb
    | true =>
      simp only [d365515, d365692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365516 q = 1) (hb : d365693 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d365516, d365693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365516, d365693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365517 q = 1) (hb : d365694 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d365517, d365694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365517, d365694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365518 q = 1) (hb : d365695 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d365518, d365695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365518, d365695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365519 q = 1) (hb : d365696 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d365519, d365696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365519, d365696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365520 q = 1) (hb : d365697 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d365520, d365697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365520, d365697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100876 (p : Pattern) (ha : d365526 p = 1) (hb : d365703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365521 q = 1) (hb : d365698 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d365521, d365698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100875 q ha hb
    | true =>
      simp only [d365521, d365698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365522 q = 1) (hb : d365699 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d365522, d365699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365522, d365699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365523 q = 1) (hb : d365700 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d365523, d365700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365523, d365700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365524 q = 1) (hb : d365701 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d365524, d365701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365524, d365701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365525 q = 1) (hb : d365702 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d365525, d365702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365525, d365702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365526 q = 1) (hb : d365703 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d365526, d365703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365526, d365703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100877 (p : Pattern) (ha : d365532 p = 1) (hb : d365709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365527 q = 1) (hb : d365704 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d365527, d365704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100876 q ha hb
    | true =>
      simp only [d365527, d365704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365528 q = 1) (hb : d365705 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d365528, d365705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365528, d365705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365529 q = 1) (hb : d365706 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d365529, d365706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365529, d365706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365530 q = 1) (hb : d365707 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d365530, d365707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365530, d365707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365531 q = 1) (hb : d365708 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d365531, d365708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365531, d365708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365532 q = 1) (hb : d365709 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d365532, d365709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365532, d365709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100878 (p : Pattern) (ha : d365538 p = 1) (hb : d365715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365533 q = 1) (hb : d365710 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d365533, d365710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100877 q ha hb
    | true =>
      simp only [d365533, d365710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365534 q = 1) (hb : d365711 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d365534, d365711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365534, d365711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365535 q = 1) (hb : d365712 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d365535, d365712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365535, d365712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365536 q = 1) (hb : d365713 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d365536, d365713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365536, d365713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365537 q = 1) (hb : d365714 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d365537, d365714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365537, d365714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365538 q = 1) (hb : d365715 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d365538, d365715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365538, d365715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100879 (p : Pattern) (ha : d365544 p = 1) (hb : d365721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365539 q = 1) (hb : d365716 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d365539, d365716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100878 q ha hb
    | true =>
      simp only [d365539, d365716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365540 q = 1) (hb : d365717 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d365540, d365717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365540, d365717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365541 q = 1) (hb : d365718 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d365541, d365718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365541, d365718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365542 q = 1) (hb : d365719 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d365542, d365719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365542, d365719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365543 q = 1) (hb : d365720 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d365543, d365720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365543, d365720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365544 q = 1) (hb : d365721 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d365544, d365721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365544, d365721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100880 (p : Pattern) (ha : d362939 p = 1) (hb : d365545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359042 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d359048 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d359076 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d365159 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d362935 q = 1) (hb : d365160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362935, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d362935, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d358966 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d362936 q = 1) (hb : d365161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362936, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d362936, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d362937 q = 1) (hb : d365162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362937, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362937, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d362938 q = 1) (hb : d365163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362938, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362938, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d362939 q = 1) (hb : d365545 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362939, d365545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362939, d365545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100881 (p : Pattern) (ha : d362944 p = 1) (hb : d365170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d359042 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359048 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d359076 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d365159 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d362935 q = 1) (hb : d365160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362935, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d362935, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d358966 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d362936 q = 1) (hb : d365161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362936, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362936, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d362937 q = 1) (hb : d365162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362937, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362937, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362938 q = 1) (hb : d365163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362938, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362938, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d359114 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d359118 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d359120 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d365165 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d362940 q = 1) (hb : d365166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362940, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d362940, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d358973 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d362941 q = 1) (hb : d365167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362941, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362941, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d362942 q = 1) (hb : d365168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362942, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d362942, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d362943 q = 1) (hb : d365169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362943, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d362943, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d362944 q = 1) (hb : d365170 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362944, d365170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d362944, d365170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100882 (p : Pattern) (ha : d362951 p = 1) (hb : d365179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d365165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362940 q = 1) (hb : d365166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362940, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362940, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d358973 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d362941 q = 1) (hb : d365167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362941, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362941, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d362949 q = 1) (hb : d365168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362949, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362949, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362950 q = 1) (hb : d365169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362950, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362950, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362951 q = 1) (hb : d365179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362951, d365179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362951, d365179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100883 (p : Pattern) (ha : d362961 p = 1) (hb : d365232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359160 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d365227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362957 q = 1) (hb : d365228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d362957, d365228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362957, d365228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d359007 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d362958 q = 1) (hb : d365229 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d362958, d365229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362958, d365229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d362959 q = 1) (hb : d365230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d362959, d365230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362959, d365230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362960 q = 1) (hb : d365231 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d362960, d365231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362960, d365231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362961 q = 1) (hb : d365232 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d362961, d365232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d362961, d365232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100884 (p : Pattern) (ha : d362967 p = 1) (hb : d365667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d359036 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d362945 q = 1) (hb : d365548 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362945, d365548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100880 q ha hb
    | true =>
      simp only [d362945, d365548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100881 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d359130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362946 q = 1) (hb : d365549 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362946, d365549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d362946, d365549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d362947 q = 1) (hb : d365657 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362947, d365657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d362947, d365657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362948 q = 1) (hb : d365658 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362948, d365658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d362948, d365658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362952 q = 1) (hb : d365180 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362952, d365180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362952, d365180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100882 q ha hb
  have h8 (q : Pattern) (ha : d362953 q = 1) (hb : d365659 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362953, d365659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d362953, d365659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d362954 q = 1) (hb : d365660 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362954, d365660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d362954, d365660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d362955 q = 1) (hb : d365661 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362955, d365661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d362955, d365661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d362956 q = 1) (hb : d365662 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d362956, d365662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d362956, d365662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d362962 q = 1) (hb : d365233 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d362962, d365233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d362962, d365233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100883 q ha hb
  have h13 (q : Pattern) (ha : d362963 q = 1) (hb : d365663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d362963, d365663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d362963, d365663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d362964 q = 1) (hb : d365664 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d362964, d365664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d362964, d365664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d362965 q = 1) (hb : d365665 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d362965, d365665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d362965, d365665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d362966 q = 1) (hb : d365666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d362966, d365666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d362966, d365666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d362967 q = 1) (hb : d365667 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d362967, d365667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d362967, d365667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro100885 (p : Pattern) (ha : d362972 p = 1) (hb : d365673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d362972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359021 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d362968 q = 1) (hb : d365668 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d362968, d365668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362968, d365668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100884 q ha hb
  have h4 (q : Pattern) (ha : d362969 q = 1) (hb : d365669 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d362969, d365669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362969, d365669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d362970 q = 1) (hb : d365670 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d362970, d365670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362970, d365670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d362971 q = 1) (hb : d365671 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d362971, d365671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d362971, d365671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d362972 q = 1) (hb : d365672 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d362972, d365672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d362972, d365672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d362972 q = 1) (hb : d365673 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d365673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d365673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100886 (p : Pattern) (ha : d365679 p = 1) (hb : d365727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365674 q = 1) (hb : d365722 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d365674, d365722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100885 q hb ha
    | true =>
      simp only [d365674, d365722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365675 q = 1) (hb : d365723 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d365675, d365723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365675, d365723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365676 q = 1) (hb : d365724 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d365676, d365724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365676, d365724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365677 q = 1) (hb : d365725 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d365677, d365725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365677, d365725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365678 q = 1) (hb : d365726 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d365678, d365726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365678, d365726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365679 q = 1) (hb : d365727 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d365679, d365727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365679, d365727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100887 (p : Pattern) (ha : d365685 p = 1) (hb : d365733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365680 q = 1) (hb : d365728 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d365680, d365728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100886 q ha hb
    | true =>
      simp only [d365680, d365728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365681 q = 1) (hb : d365729 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d365681, d365729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365681, d365729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365682 q = 1) (hb : d365730 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d365682, d365730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365682, d365730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365683 q = 1) (hb : d365731 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d365683, d365731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365683, d365731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365684 q = 1) (hb : d365732 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d365684, d365732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365684, d365732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365685 q = 1) (hb : d365733 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d365685, d365733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365685, d365733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100888 (p : Pattern) (ha : d365691 p = 1) (hb : d365739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365686 q = 1) (hb : d365734 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d365686, d365734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100887 q ha hb
    | true =>
      simp only [d365686, d365734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365687 q = 1) (hb : d365735 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d365687, d365735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365687, d365735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365688 q = 1) (hb : d365736 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d365688, d365736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365688, d365736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365689 q = 1) (hb : d365737 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d365689, d365737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365689, d365737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365690 q = 1) (hb : d365738 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d365690, d365738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365690, d365738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365691 q = 1) (hb : d365739 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d365691, d365739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365691, d365739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100889 (p : Pattern) (ha : d365697 p = 1) (hb : d365745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365692 q = 1) (hb : d365740 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d365692, d365740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100888 q ha hb
    | true =>
      simp only [d365692, d365740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365693 q = 1) (hb : d365741 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d365693, d365741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365693, d365741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365694 q = 1) (hb : d365742 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d365694, d365742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365694, d365742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365695 q = 1) (hb : d365743 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d365695, d365743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365695, d365743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365696 q = 1) (hb : d365744 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d365696, d365744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365696, d365744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365697 q = 1) (hb : d365745 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d365697, d365745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365697, d365745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100890 (p : Pattern) (ha : d365703 p = 1) (hb : d365751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365698 q = 1) (hb : d365746 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d365698, d365746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100889 q ha hb
    | true =>
      simp only [d365698, d365746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365699 q = 1) (hb : d365747 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d365699, d365747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365699, d365747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365700 q = 1) (hb : d365748 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d365700, d365748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365700, d365748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365701 q = 1) (hb : d365749 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d365701, d365749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365701, d365749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365702 q = 1) (hb : d365750 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d365702, d365750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365702, d365750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365703 q = 1) (hb : d365751 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d365703, d365751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365703, d365751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100891 (p : Pattern) (ha : d365709 p = 1) (hb : d365757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365704 q = 1) (hb : d365752 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d365704, d365752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100890 q ha hb
    | true =>
      simp only [d365704, d365752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365705 q = 1) (hb : d365753 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d365705, d365753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365705, d365753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365706 q = 1) (hb : d365754 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d365706, d365754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365706, d365754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365707 q = 1) (hb : d365755 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d365707, d365755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365707, d365755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365708 q = 1) (hb : d365756 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d365708, d365756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365708, d365756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365709 q = 1) (hb : d365757 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d365709, d365757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365709, d365757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100892 (p : Pattern) (ha : d365715 p = 1) (hb : d365763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365710 q = 1) (hb : d365758 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d365710, d365758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100891 q ha hb
    | true =>
      simp only [d365710, d365758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365711 q = 1) (hb : d365759 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d365711, d365759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365711, d365759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365712 q = 1) (hb : d365760 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d365712, d365760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365712, d365760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365713 q = 1) (hb : d365761 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d365713, d365761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365713, d365761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365714 q = 1) (hb : d365762 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d365714, d365762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365714, d365762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365715 q = 1) (hb : d365763 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d365715, d365763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365715, d365763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100893 (p : Pattern) (ha : d365721 p = 1) (hb : d365769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365716 q = 1) (hb : d365764 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d365716, d365764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100892 q ha hb
    | true =>
      simp only [d365716, d365764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d365717 q = 1) (hb : d365765 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d365717, d365765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365717, d365765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d365718 q = 1) (hb : d365766 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d365718, d365766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365718, d365766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d365719 q = 1) (hb : d365767 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d365719, d365767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365719, d365767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d365720 q = 1) (hb : d365768 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d365720, d365768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365720, d365768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d365721 q = 1) (hb : d365769 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d365721, d365769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365721, d365769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100894 (p : Pattern) (ha : d104 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100895 (p : Pattern) (ha : d213 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100896 (p : Pattern) (ha : d308 p = 1) (hb : d309771 p = 1) : d365911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100806 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100807 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42274 q = 1) : d365159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100801 q ha hb
    | true =>
      simp only [d42274, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309767 q = 1) : d365559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309767, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309767, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309768 q = 1) : d365908 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309768, d365908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309768, d365908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309769 q = 1) : d365909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309769, d365909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d309769, d365909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309770 q = 1) : d365910 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309770, d365910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309770, d365910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d309771 q = 1) : d365911 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309771, d365911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309771, d365911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100897 (p : Pattern) (ha : d308 p = 1) (hb : d309776 p = 1) : d365915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100806 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100807 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42274 q = 1) : d365159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100801 q ha hb
    | true =>
      simp only [d42274, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309767 q = 1) : d365559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309767, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309767, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309768 q = 1) : d365908 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309768, d365908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309768, d365908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309769 q = 1) : d365909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309769, d365909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d309769, d365909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309770 q = 1) : d365910 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309770, d365910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309770, d365910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100814 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100815 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d42281 q = 1) : d365165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100803 q ha hb
    | true =>
      simp only [d42281, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100794 q hb ha
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d309772 q = 1) : d365572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309772, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309772, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100794 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d309773 q = 1) : d365912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309773, d365912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309773, d365912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d309774 q = 1) : d365913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309774, d365913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d309774, d365913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d308 q = 1) (hb : d309775 q = 1) : d365914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309775, d365914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d309775, d365914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d308 q = 1) (hb : d309776 q = 1) : d365915 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309776, d365915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309776, d365915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro100898 (p : Pattern) (ha : d308 p = 1) (hb : d309783 p = 1) : d365920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42281 q = 1) : d365165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100803 q ha hb
    | true =>
      simp only [d42281, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100794 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309772 q = 1) : d365572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309772, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309772, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100794 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309773 q = 1) : d365912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309773, d365912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309773, d365912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309781 q = 1) : d365913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309781, d365913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309781, d365913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d309782 q = 1) : d365914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309782, d365914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309782, d365914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309783 q = 1) : d365920 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309783, d365920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309783, d365920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100899 (p : Pattern) (ha : d308 p = 1) (hb : d309793 p = 1) : d365929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42317 q = 1) : d365227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42317, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100823 q ha hb
    | true =>
      simp only [d42317, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100798 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309789 q = 1) : d365592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309789, d365592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309789, d365592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100798 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309790 q = 1) : d365926 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309790, d365926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309790, d365926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309791 q = 1) : d365927 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309791, d365927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309791, d365927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d309792 q = 1) : d365928 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309792, d365928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309792, d365928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309793 q = 1) : d365929 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309793, d365929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309793, d365929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100900 (p : Pattern) (ha : d308 p = 1) (hb : d309799 p = 1) : d365935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100894 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100894 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100795 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309777 q = 1) : d365916 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309777, d365916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100896 q ha hb
    | true =>
      simp only [d309777, d365916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100897 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100895 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309778 q = 1) : d365917 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309778, d365917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309778, d365917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309779 q = 1) : d365918 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309779, d365918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309779, d365918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d309780 q = 1) : d365919 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309780, d365919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d309780, d365919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d309784 q = 1) : d365921 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309784, d365921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309784, d365921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100898 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309785 q = 1) : d365922 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309785, d365922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309785, d365922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309786 q = 1) : d365923 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309786, d365923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309786, d365923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309787 q = 1) : d365924 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309787, d365924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309787, d365924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d309788 q = 1) : d365925 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309788, d365925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309788, d365925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d309794 q = 1) : d365930 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309794, d365930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309794, d365930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100899 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d309795 q = 1) : d365931 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309795, d365931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309795, d365931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d309796 q = 1) : d365932 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309796, d365932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309796, d365932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d309797 q = 1) : d365933 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309797, d365933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309797, d365933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d309798 q = 1) : d365934 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309798, d365934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309798, d365934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d309799 q = 1) : d365935 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309799, d365935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309799, d365935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro100901 (p : Pattern) (ha : d309843 p = 1) (hb : d365796 p = 1) : d365941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309800 q = 1) : d365936 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309800, d365936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309800, d365936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100900 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d309801 q = 1) : d365937 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309801, d365937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309801, d365937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d309802 q = 1) : d365938 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309802, d365938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309802, d365938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309803 q = 1) : d365939 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309803, d365939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309803, d365939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309804 q = 1) (hb : d365795 q = 1) : d365940 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309804, d365795, d365940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309804, d365795, d365940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d309842 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d309843 q = 1) (hb : d365796 q = 1) : d365941 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d365796, d365941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309843, d365796, d365941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro100902 (p : Pattern) (ha : d310011 p = 1) (hb : d365801 p = 1) : d365947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d309882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309883 q = 1) (hb : d365797 q = 1) : d365942 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309883, d365797, d365942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100901 q ha hb
    | true =>
      simp only [d309883, d365797, d365942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309923 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309924 q = 1) (hb : d365798 q = 1) : d365943 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309924, d365798, d365943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309924, d365798, d365943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d309965 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309966 q = 1) (hb : d365799 q = 1) : d365944 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d365799, d365944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309966, d365799, d365944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d310008 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310009 q = 1) (hb : d365800 q = 1) : d365945 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d365800, d365945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310009, d365800, d365945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d310010 q = 1) (hb : d365801 q = 1) : d365946 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d365801, d365946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d310010, d365801, d365946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d365801 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d310011 q = 1) (hb : d365801 q = 1) : d365947 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, d365947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d310011, d365947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100903 (p : Pattern) (ha : d310017 p = 1) (hb : d365804 p = 1) : d365953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365801 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d365801 q = 1) : d365948 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, d365948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100902 q ha hb
    | true =>
      simp only [d310012, d365948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d365801 q = 1) : d365949 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d365949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d365949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310014 q = 1) (hb : d365801 q = 1) : d365950 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d365950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d365950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d310015 q = 1) (hb : d365802 q = 1) : d365951 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d365802, d365951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310015, d365802, d365951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310016 q = 1) (hb : d365803 q = 1) : d365952 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d365803, d365952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310016, d365803, d365952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d310017 q = 1) (hb : d365804 q = 1) : d365953 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d365804, d365953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d310017, d365804, d365953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h7 p ha hb
theorem andIntro100904 (p : Pattern) (ha : d310023 p = 1) (hb : d365809 p = 1) : d365959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d365805 q = 1) : d365954 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d365805, d365954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100903 q ha hb
    | true =>
      simp only [d310018, d365805, d365954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d365806 q = 1) : d365955 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d365806, d365955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d365806, d365955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310020 q = 1) (hb : d365807 q = 1) : d365956 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d365807, d365956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d365807, d365956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310021 q = 1) (hb : d365808 q = 1) : d365957 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d365808, d365957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310021, d365808, d365957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310022 q = 1) (hb : d365809 q = 1) : d365958 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d365809, d365958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310022, d365809, d365958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310023 q = 1) (hb : d365809 q = 1) : d365959 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, d365959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310023, d365959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100905 (p : Pattern) (ha : d310029 p = 1) (hb : d365809 p = 1) : d365965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d365809 q = 1) : d365960 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, d365960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100904 q ha hb
    | true =>
      simp only [d310024, d365960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d365809 q = 1) : d365961 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, d365961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, d365961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d365809 q = 1) : d365962 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, d365962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, d365962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d365809 q = 1) : d365963 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, d365963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, d365963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d365809 q = 1) : d365964 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, d365964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, d365964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d365809 q = 1) : d365965 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, d365965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, d365965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100906 (p : Pattern) (ha : d310035 p = 1) (hb : d365809 p = 1) : d365971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d365809 q = 1) : d365966 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, d365966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100905 q ha hb
    | true =>
      simp only [d310030, d365966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d365809 q = 1) : d365967 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, d365967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, d365967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d365809 q = 1) : d365968 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, d365968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, d365968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d365809 q = 1) : d365969 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, d365969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, d365969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d365809 q = 1) : d365970 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, d365970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, d365970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d365809 q = 1) : d365971 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, d365971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, d365971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100907 (p : Pattern) (ha : d310041 p = 1) (hb : d365809 p = 1) : d365977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d365809 q = 1) : d365972 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, d365972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100906 q ha hb
    | true =>
      simp only [d310036, d365972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d365809 q = 1) : d365973 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, d365973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, d365973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d365809 q = 1) : d365974 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, d365974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, d365974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d365809 q = 1) : d365975 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, d365975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, d365975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d365809 q = 1) : d365976 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, d365976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, d365976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d365809 q = 1) : d365977 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, d365977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, d365977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100908 (p : Pattern) (ha : d310047 p = 1) (hb : d365809 p = 1) : d365983 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d365809 q = 1) : d365978 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, d365978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100907 q ha hb
    | true =>
      simp only [d310042, d365978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d365809 q = 1) : d365979 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, d365979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, d365979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d365809 q = 1) : d365980 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, d365980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, d365980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d365809 q = 1) : d365981 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, d365981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, d365981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d365809 q = 1) : d365982 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, d365982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, d365982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d365809 q = 1) : d365983 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, d365983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, d365983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100909 (p : Pattern) (ha : d310053 p = 1) (hb : d365809 p = 1) : d365989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d365809 q = 1) : d365984 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, d365984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100908 q ha hb
    | true =>
      simp only [d310048, d365984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d365809 q = 1) : d365985 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, d365985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, d365985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d365809 q = 1) : d365986 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, d365986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, d365986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d365809 q = 1) : d365987 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, d365987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, d365987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d365809 q = 1) : d365988 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, d365988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, d365988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d365809 q = 1) : d365989 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, d365989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, d365989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100910 (p : Pattern) (ha : d361223 p = 1) (hb : d365911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361218 q = 1) (hb : d365159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
    | true =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361219 q = 1) (hb : d365559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361219, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361219, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361220 q = 1) (hb : d365908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361220, d365908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361220, d365908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361221 q = 1) (hb : d365909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361221, d365909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361221, d365909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361222 q = 1) (hb : d365910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361222, d365910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361222, d365910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361223 q = 1) (hb : d365911 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361223, d365911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361223, d365911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100911 (p : Pattern) (ha : d361230 p = 1) (hb : d365915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361218 q = 1) (hb : d365159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
    | true =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361219 q = 1) (hb : d365559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361219, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361219, d365559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361220 q = 1) (hb : d365908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361220, d365908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361220, d365908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361221 q = 1) (hb : d365909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361221, d365909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361221, d365909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361222 q = 1) (hb : d365910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361222, d365910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361222, d365910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361225 q = 1) (hb : d365165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
    | true =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361226 q = 1) (hb : d365572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361226, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361226, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361227 q = 1) (hb : d365912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361227, d365912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361227, d365912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361228 q = 1) (hb : d365913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361228, d365913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361228, d365913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361229 q = 1) (hb : d365914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361229, d365914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361229, d365914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361230 q = 1) (hb : d365915 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361230, d365915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361230, d365915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100912 (p : Pattern) (ha : d361235 p = 1) (hb : d365920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361225 q = 1) (hb : d365165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
    | true =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361226 q = 1) (hb : d365572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361226, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361226, d365572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361227 q = 1) (hb : d365912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361227, d365912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361227, d365912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361228 q = 1) (hb : d365913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361228, d365913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361228, d365913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361229 q = 1) (hb : d365914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361229, d365914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361229, d365914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361235 q = 1) (hb : d365920 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361235, d365920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361235, d365920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100913 (p : Pattern) (ha : d361264 p = 1) (hb : d365929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361259 q = 1) (hb : d365227 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361259, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100740 q ha hb
    | true =>
      simp only [d361259, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361260 q = 1) (hb : d365592 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361260, d365592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361260, d365592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361261 q = 1) (hb : d365926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361261, d365926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361261, d365926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361262 q = 1) (hb : d365927 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361262, d365927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361262, d365927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361263 q = 1) (hb : d365928 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361263, d365928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361263, d365928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361264 q = 1) (hb : d365929 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361264, d365929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361264, d365929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100914 (p : Pattern) (ha : d361270 p = 1) (hb : d365935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361231 q = 1) (hb : d365916 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361231, d365916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100910 q ha hb
    | true =>
      simp only [d361231, d365916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100911 q ha hb
  have h2 (q : Pattern) (ha : d361232 q = 1) (hb : d365917 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361232, d365917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361232, d365917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361233 q = 1) (hb : d365918 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361233, d365918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361233, d365918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361234 q = 1) (hb : d365919 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361234, d365919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361234, d365919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361236 q = 1) (hb : d365921 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361236, d365921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361236, d365921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100912 q ha hb
  have h6 (q : Pattern) (ha : d361237 q = 1) (hb : d365922 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361237, d365922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361237, d365922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361238 q = 1) (hb : d365923 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361238, d365923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361238, d365923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361239 q = 1) (hb : d365924 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361239, d365924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361239, d365924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361240 q = 1) (hb : d365925 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361240, d365925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361240, d365925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361265 q = 1) (hb : d365930 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361265, d365930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361265, d365930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100913 q ha hb
  have h11 (q : Pattern) (ha : d361266 q = 1) (hb : d365931 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361266, d365931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361266, d365931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361267 q = 1) (hb : d365932 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361267, d365932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361267, d365932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361268 q = 1) (hb : d365933 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361268, d365933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361268, d365933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d361269 q = 1) (hb : d365934 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361269, d365934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361269, d365934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d361270 q = 1) (hb : d365935 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d361270, d365935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361270, d365935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100915 (p : Pattern) (ha : d365859 p = 1) (hb : d365941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361274 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d361271 q = 1) (hb : d365936 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d361271, d365936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361271, d365936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100914 q ha hb
  have h3 (q : Pattern) (ha : d361272 q = 1) (hb : d365937 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d361272, d365937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361272, d365937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361273 q = 1) (hb : d365938 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d361273, d365938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361273, d365938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361274 q = 1) (hb : d365939 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d361274, d365939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361274, d365939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361274 q = 1) (hb : d365940 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d365940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d365940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d365859 q = 1) (hb : d365941 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d365859, d365941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d365859, d365941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro100916 (p : Pattern) (ha : d365865 p = 1) (hb : d365947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365860 q = 1) (hb : d365942 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d365860, d365942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100915 q ha hb
    | true =>
      simp only [d365860, d365942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365861 q = 1) (hb : d365943 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d365861, d365943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365861, d365943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365862 q = 1) (hb : d365944 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d365862, d365944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365862, d365944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365863 q = 1) (hb : d365945 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d365863, d365945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365863, d365945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365864 q = 1) (hb : d365946 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d365864, d365946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365864, d365946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365865 q = 1) (hb : d365947 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d365865, d365947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365865, d365947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100917 (p : Pattern) (ha : d365871 p = 1) (hb : d365953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365866 q = 1) (hb : d365948 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d365866, d365948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100916 q ha hb
    | true =>
      simp only [d365866, d365948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365867 q = 1) (hb : d365949 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d365867, d365949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365867, d365949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365868 q = 1) (hb : d365950 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d365868, d365950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365868, d365950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365869 q = 1) (hb : d365951 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d365869, d365951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365869, d365951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365870 q = 1) (hb : d365952 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d365870, d365952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365870, d365952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365871 q = 1) (hb : d365953 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d365871, d365953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365871, d365953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100918 (p : Pattern) (ha : d365877 p = 1) (hb : d365959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365872 q = 1) (hb : d365954 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d365872, d365954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100917 q ha hb
    | true =>
      simp only [d365872, d365954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365873 q = 1) (hb : d365955 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d365873, d365955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365873, d365955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365874 q = 1) (hb : d365956 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d365874, d365956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365874, d365956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365875 q = 1) (hb : d365957 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d365875, d365957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365875, d365957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365876 q = 1) (hb : d365958 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d365876, d365958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365876, d365958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365877 q = 1) (hb : d365959 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d365877, d365959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365877, d365959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100919 (p : Pattern) (ha : d365883 p = 1) (hb : d365965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365878 q = 1) (hb : d365960 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d365878, d365960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100918 q ha hb
    | true =>
      simp only [d365878, d365960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365879 q = 1) (hb : d365961 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d365879, d365961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365879, d365961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365880 q = 1) (hb : d365962 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d365880, d365962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365880, d365962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365881 q = 1) (hb : d365963 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d365881, d365963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365881, d365963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365882 q = 1) (hb : d365964 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d365882, d365964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365882, d365964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365883 q = 1) (hb : d365965 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d365883, d365965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365883, d365965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100920 (p : Pattern) (ha : d365889 p = 1) (hb : d365971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365884 q = 1) (hb : d365966 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d365884, d365966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100919 q ha hb
    | true =>
      simp only [d365884, d365966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365885 q = 1) (hb : d365967 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d365885, d365967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365885, d365967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365886 q = 1) (hb : d365968 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d365886, d365968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365886, d365968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365887 q = 1) (hb : d365969 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d365887, d365969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365887, d365969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365888 q = 1) (hb : d365970 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d365888, d365970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365888, d365970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365889 q = 1) (hb : d365971 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d365889, d365971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365889, d365971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100921 (p : Pattern) (ha : d365895 p = 1) (hb : d365977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365890 q = 1) (hb : d365972 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d365890, d365972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100920 q ha hb
    | true =>
      simp only [d365890, d365972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365891 q = 1) (hb : d365973 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d365891, d365973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365891, d365973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365892 q = 1) (hb : d365974 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d365892, d365974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365892, d365974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365893 q = 1) (hb : d365975 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d365893, d365975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365893, d365975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365894 q = 1) (hb : d365976 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d365894, d365976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365894, d365976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365895 q = 1) (hb : d365977 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d365895, d365977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365895, d365977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100922 (p : Pattern) (ha : d365901 p = 1) (hb : d365983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365896 q = 1) (hb : d365978 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d365896, d365978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100921 q ha hb
    | true =>
      simp only [d365896, d365978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365897 q = 1) (hb : d365979 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d365897, d365979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365897, d365979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365898 q = 1) (hb : d365980 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d365898, d365980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365898, d365980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365899 q = 1) (hb : d365981 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d365899, d365981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365899, d365981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365900 q = 1) (hb : d365982 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d365900, d365982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365900, d365982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365901 q = 1) (hb : d365983 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d365901, d365983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365901, d365983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100923 (p : Pattern) (ha : d365907 p = 1) (hb : d365989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365902 q = 1) (hb : d365984 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d365902, d365984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100922 q ha hb
    | true =>
      simp only [d365902, d365984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365903 q = 1) (hb : d365985 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d365903, d365985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365903, d365985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365904 q = 1) (hb : d365986 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d365904, d365986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365904, d365986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365905 q = 1) (hb : d365987 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d365905, d365987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365905, d365987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365906 q = 1) (hb : d365988 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d365906, d365988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365906, d365988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365907 q = 1) (hb : d365989 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d365907, d365989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365907, d365989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100924 (p : Pattern) (ha : d308 p = 1) (hb : d53647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100894 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100795 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d53637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d53638 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100796 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d53639 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d53640 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d53641 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d53642 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100799 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d53643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d53644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d53645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d53646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d53647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100925 (p : Pattern) (ha : d357440 p = 1) (hb : d365796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100924 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d365795 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d365795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d365795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d357439 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d357440 q = 1) (hb : d365796 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357440, d365796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357440, d365796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro100926 (p : Pattern) (ha : d357556 p = 1) (hb : d365801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d357466 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357467 q = 1) (hb : d365797 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357467, d365797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100925 q ha hb
    | true =>
      simp only [d357467, d365797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d357494 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d357495 q = 1) (hb : d365798 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357495, d365798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357495, d365798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d357523 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d357524 q = 1) (hb : d365799 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357524, d365799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357524, d365799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d357553 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357554 q = 1) (hb : d365800 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d357554, d365800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357554, d365800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d357555 q = 1) (hb : d365801 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d365801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357555, d365801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d365801 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d357556 q = 1) (hb : d365801 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100927 (p : Pattern) (ha : d357562 p = 1) (hb : d365804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365801 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357557 q = 1) (hb : d365801 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100926 q ha hb
    | true =>
      simp only [d357557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357558 q = 1) (hb : d365801 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357559 q = 1) (hb : d365801 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d357560 q = 1) (hb : d365802 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d365802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357560, d365802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d357561 q = 1) (hb : d365803 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d365803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357561, d365803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d357562 q = 1) (hb : d365804 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d365804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357562, d365804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h7 p ha hb
theorem andIntro100928 (p : Pattern) (ha : d357568 p = 1) (hb : d365809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357563 q = 1) (hb : d365805 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d365805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100927 q ha hb
    | true =>
      simp only [d357563, d365805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357564 q = 1) (hb : d365806 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d365806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d365806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357565 q = 1) (hb : d365807 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d365807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357565, d365807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357566 q = 1) (hb : d365808 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d365808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357566, d365808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357567 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d365809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357567, d365809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357568 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100929 (p : Pattern) (ha : d357574 p = 1) (hb : d365809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357569 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100928 q ha hb
    | true =>
      simp only [d357569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357570 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357571 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357572 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357573 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357574 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100930 (p : Pattern) (ha : d357580 p = 1) (hb : d365809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357575 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100929 q ha hb
    | true =>
      simp only [d357575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357576 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357577 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357578 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357579 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357580 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100931 (p : Pattern) (ha : d357586 p = 1) (hb : d365809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357581 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100930 q ha hb
    | true =>
      simp only [d357581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357582 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357583 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357584 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357585 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357586 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100932 (p : Pattern) (ha : d357592 p = 1) (hb : d365809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357587 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100931 q ha hb
    | true =>
      simp only [d357587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357588 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357589 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357590 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357591 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357592 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100933 (p : Pattern) (ha : d357598 p = 1) (hb : d365809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357593 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100932 q ha hb
    | true =>
      simp only [d357593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357594 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357595 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357596 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357597 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357598 q = 1) (hb : d365809 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100934 (p : Pattern) (ha : d0 p = 1) (hb : d365907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365907 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro100935 (p : Pattern) (ha : d0 p = 1) (hb : d365858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d365858 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro100936 (p : Pattern) (ha : d48 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100937 (p : Pattern) (ha : d55 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100793 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100794 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100938 (p : Pattern) (ha : d60 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100794 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100939 (p : Pattern) (ha : d89 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100798 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100940 (p : Pattern) (ha : d95 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100936 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100937 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100938 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100939 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
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
theorem andIntro100941 (p : Pattern) (ha : d309843 p = 1) (hb : d366020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100940 q ha hb
  have h3 (q : Pattern) (ha : d97 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d98 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99 q = 1) (hb : d366018 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d366018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d366018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d309803 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309804 q = 1) (hb : d366019 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309804, d366019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309804, d366019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309842 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309843 q = 1) (hb : d366020 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d366020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309843, d366020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro100942 (p : Pattern) (ha : d310011 p = 1) (hb : d366025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d309882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309883 q = 1) (hb : d366021 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309883, d366021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100941 q ha hb
    | true =>
      simp only [d309883, d366021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309923 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309924 q = 1) (hb : d366022 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309924, d366022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309924, d366022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d309965 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309966 q = 1) (hb : d366023 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d366023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309966, d366023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d310008 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310009 q = 1) (hb : d366024 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d366024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310009, d366024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d310010 q = 1) (hb : d366025 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d366025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d310010, d366025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d366025 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d310011 q = 1) (hb : d366025 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d310011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100943 (p : Pattern) (ha : d310017 p = 1) (hb : d366029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366025 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d366025 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100942 q ha hb
    | true =>
      simp only [d310012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d366025 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d310014 q = 1) (hb : d366026 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d366026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d366026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310015 q = 1) (hb : d366027 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d366027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310015, d366027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d310016 q = 1) (hb : d366028 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d366028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310016, d366028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d310017 q = 1) (hb : d366029 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d366029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d310017, d366029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro100944 (p : Pattern) (ha : d310023 p = 1) (hb : d366034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d366030 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d366030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100943 q ha hb
    | true =>
      simp only [d310018, d366030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d366031 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d366031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d366031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310020 q = 1) (hb : d366032 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d366032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d366032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310021 q = 1) (hb : d366033 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d366033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310021, d366033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310022 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d366034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310022, d366034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310023 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100945 (p : Pattern) (ha : d310029 p = 1) (hb : d366034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100944 q ha hb
    | true =>
      simp only [d310024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100946 (p : Pattern) (ha : d310035 p = 1) (hb : d366034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100945 q ha hb
    | true =>
      simp only [d310030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100947 (p : Pattern) (ha : d310041 p = 1) (hb : d366034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100946 q ha hb
    | true =>
      simp only [d310036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100948 (p : Pattern) (ha : d310047 p = 1) (hb : d366034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100947 q ha hb
    | true =>
      simp only [d310042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100949 (p : Pattern) (ha : d310053 p = 1) (hb : d366034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100948 q ha hb
    | true =>
      simp only [d310048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100950 (p : Pattern) (ha : d357440 p = 1) (hb : d366020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366018 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53652 q = 1) (hb : d366019 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d366019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d366019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d357439 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d357440 q = 1) (hb : d366020 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357440, d366020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357440, d366020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro100951 (p : Pattern) (ha : d357556 p = 1) (hb : d366025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d357466 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357467 q = 1) (hb : d366021 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357467, d366021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100950 q ha hb
    | true =>
      simp only [d357467, d366021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d357494 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d357495 q = 1) (hb : d366022 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357495, d366022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357495, d366022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d357523 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d357524 q = 1) (hb : d366023 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357524, d366023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357524, d366023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d357553 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357554 q = 1) (hb : d366024 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d357554, d366024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357554, d366024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d357555 q = 1) (hb : d366025 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d366025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357555, d366025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d366025 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d357556 q = 1) (hb : d366025 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100952 (p : Pattern) (ha : d357562 p = 1) (hb : d366029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366025 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357557 q = 1) (hb : d366025 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100951 q ha hb
    | true =>
      simp only [d357557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357558 q = 1) (hb : d366025 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d357559 q = 1) (hb : d366026 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, d366026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357559, d366026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d357560 q = 1) (hb : d366027 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d366027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357560, d366027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d357561 q = 1) (hb : d366028 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d366028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357561, d366028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d357562 q = 1) (hb : d366029 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d366029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357562, d366029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro100953 (p : Pattern) (ha : d357568 p = 1) (hb : d366034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357563 q = 1) (hb : d366030 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d366030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100952 q ha hb
    | true =>
      simp only [d357563, d366030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357564 q = 1) (hb : d366031 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d366031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d366031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357565 q = 1) (hb : d366032 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d366032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357565, d366032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357566 q = 1) (hb : d366033 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d366033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357566, d366033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357567 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d366034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357567, d366034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357568 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100954 (p : Pattern) (ha : d357574 p = 1) (hb : d366034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357569 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100953 q ha hb
    | true =>
      simp only [d357569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357570 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357571 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357572 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357573 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357574 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100955 (p : Pattern) (ha : d357580 p = 1) (hb : d366034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357575 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100954 q ha hb
    | true =>
      simp only [d357575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357576 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357577 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357578 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357579 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357580 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100956 (p : Pattern) (ha : d357586 p = 1) (hb : d366034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357581 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100955 q ha hb
    | true =>
      simp only [d357581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357582 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357583 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357584 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357585 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357586 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100957 (p : Pattern) (ha : d357592 p = 1) (hb : d366034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357587 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100956 q ha hb
    | true =>
      simp only [d357587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357588 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357589 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357590 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357591 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357592 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100958 (p : Pattern) (ha : d357598 p = 1) (hb : d366034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357593 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100957 q ha hb
    | true =>
      simp only [d357593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357594 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357595 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357596 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357597 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357598 q = 1) (hb : d366034 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100959 (p : Pattern) (ha : d309843 p = 1) (hb : d366069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d98 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d99 q = 1) (hb : d366067 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d366067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d366067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d309803 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309804 q = 1) (hb : d366068 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309804, d366068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309804, d366068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d309842 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309843 q = 1) (hb : d366069 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d366069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309843, d366069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro100960 (p : Pattern) (ha : d310011 p = 1) (hb : d366074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d309882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309883 q = 1) (hb : d366070 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309883, d366070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100959 q ha hb
    | true =>
      simp only [d309883, d366070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309923 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309924 q = 1) (hb : d366071 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309924, d366071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309924, d366071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d309965 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309966 q = 1) (hb : d366072 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d366072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309966, d366072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d310008 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310009 q = 1) (hb : d366073 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d366073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310009, d366073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d310010 q = 1) (hb : d366074 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d366074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d310010, d366074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d366074 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d310011 q = 1) (hb : d366074 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d310011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100961 (p : Pattern) (ha : d310017 p = 1) (hb : d366079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366074 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d366074 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100960 q ha hb
    | true =>
      simp only [d310012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d310013 q = 1) (hb : d366075 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d366075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d366075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310014 q = 1) (hb : d366076 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d366076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310014, d366076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d310015 q = 1) (hb : d366077 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d366077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310015, d366077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d310016 q = 1) (hb : d366078 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d366078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310016, d366078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d310017 q = 1) (hb : d366079 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d366079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d310017, d366079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro100962 (p : Pattern) (ha : d310023 p = 1) (hb : d366084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d366080 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d366080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100961 q ha hb
    | true =>
      simp only [d310018, d366080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d366081 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d366081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d366081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310020 q = 1) (hb : d366082 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d366082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d366082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310021 q = 1) (hb : d366083 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d366083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310021, d366083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310022 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d366084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310022, d366084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310023 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100963 (p : Pattern) (ha : d310029 p = 1) (hb : d366084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100962 q ha hb
    | true =>
      simp only [d310024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100964 (p : Pattern) (ha : d310035 p = 1) (hb : d366084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100963 q ha hb
    | true =>
      simp only [d310030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100965 (p : Pattern) (ha : d310041 p = 1) (hb : d366084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100964 q ha hb
    | true =>
      simp only [d310036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100966 (p : Pattern) (ha : d310047 p = 1) (hb : d366084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100965 q ha hb
    | true =>
      simp only [d310042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100967 (p : Pattern) (ha : d310053 p = 1) (hb : d366084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100966 q ha hb
    | true =>
      simp only [d310048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100968 (p : Pattern) (ha : d357440 p = 1) (hb : d366069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366067 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53652 q = 1) (hb : d366068 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d366068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d366068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d357439 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d357440 q = 1) (hb : d366069 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357440, d366069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357440, d366069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro100969 (p : Pattern) (ha : d357556 p = 1) (hb : d366074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d357466 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357467 q = 1) (hb : d366070 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357467, d366070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100968 q ha hb
    | true =>
      simp only [d357467, d366070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d357494 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d357495 q = 1) (hb : d366071 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357495, d366071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357495, d366071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d357523 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d357524 q = 1) (hb : d366072 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357524, d366072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357524, d366072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d357553 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357554 q = 1) (hb : d366073 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d357554, d366073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357554, d366073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d357555 q = 1) (hb : d366074 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d366074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357555, d366074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d366074 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d357556 q = 1) (hb : d366074 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100970 (p : Pattern) (ha : d357562 p = 1) (hb : d366079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366074 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357557 q = 1) (hb : d366074 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100969 q ha hb
    | true =>
      simp only [d357557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d357558 q = 1) (hb : d366075 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, d366075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, d366075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d357559 q = 1) (hb : d366076 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, d366076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357559, d366076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d357560 q = 1) (hb : d366077 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d366077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357560, d366077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d357561 q = 1) (hb : d366078 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d366078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357561, d366078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d357562 q = 1) (hb : d366079 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d366079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357562, d366079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro100971 (p : Pattern) (ha : d357568 p = 1) (hb : d366084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357563 q = 1) (hb : d366080 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d366080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100970 q ha hb
    | true =>
      simp only [d357563, d366080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357564 q = 1) (hb : d366081 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d366081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d366081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357565 q = 1) (hb : d366082 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d366082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357565, d366082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357566 q = 1) (hb : d366083 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d366083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357566, d366083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357567 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d366084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357567, d366084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357568 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100972 (p : Pattern) (ha : d357574 p = 1) (hb : d366084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357569 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100971 q ha hb
    | true =>
      simp only [d357569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357570 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357571 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357572 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357573 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357574 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100973 (p : Pattern) (ha : d357580 p = 1) (hb : d366084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357575 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100972 q ha hb
    | true =>
      simp only [d357575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357576 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357577 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357578 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357579 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357580 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100974 (p : Pattern) (ha : d357586 p = 1) (hb : d366084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357581 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100973 q ha hb
    | true =>
      simp only [d357581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357582 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357583 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357584 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357585 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357586 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100975 (p : Pattern) (ha : d357592 p = 1) (hb : d366084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357587 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100974 q ha hb
    | true =>
      simp only [d357587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357588 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357589 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357590 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357591 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357592 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100976 (p : Pattern) (ha : d357598 p = 1) (hb : d366084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357593 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100975 q ha hb
    | true =>
      simp only [d357593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357594 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357595 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357596 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357597 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357598 q = 1) (hb : d366084 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100977 (p : Pattern) (ha : d309843 p = 1) (hb : d366123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d98 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d99 q = 1) (hb : d366121 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d366121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d366121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d309803 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309804 q = 1) (hb : d366122 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309804, d366122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309804, d366122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d309842 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309843 q = 1) (hb : d366123 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d366123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309843, d366123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro100978 (p : Pattern) (ha : d310011 p = 1) (hb : d366128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d309882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309883 q = 1) (hb : d366124 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309883, d366124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100977 q ha hb
    | true =>
      simp only [d309883, d366124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309923 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309924 q = 1) (hb : d366125 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309924, d366125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309924, d366125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d309965 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309966 q = 1) (hb : d366126 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d366126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309966, d366126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d310008 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310009 q = 1) (hb : d366127 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d366127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310009, d366127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d310010 q = 1) (hb : d366128 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d366128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d310010, d366128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d366128 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d310011 q = 1) (hb : d366128 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d310011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100979 (p : Pattern) (ha : d310017 p = 1) (hb : d366134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d366129 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, d366129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100978 q ha hb
    | true =>
      simp only [d310012, d366129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d366130 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d366130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d366130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310014 q = 1) (hb : d366131 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d366131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d366131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310015 q = 1) (hb : d366132 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d366132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310015, d366132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310016 q = 1) (hb : d366133 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d366133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310016, d366133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310017 q = 1) (hb : d366134 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d366134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310017, d366134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100980 (p : Pattern) (ha : d310023 p = 1) (hb : d366139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d366135 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d366135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100979 q ha hb
    | true =>
      simp only [d310018, d366135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d366136 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d366136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d366136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310020 q = 1) (hb : d366137 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d366137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d366137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310021 q = 1) (hb : d366138 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d366138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310021, d366138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310022 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d366139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310022, d366139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310023 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100981 (p : Pattern) (ha : d310029 p = 1) (hb : d366139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100980 q ha hb
    | true =>
      simp only [d310024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100982 (p : Pattern) (ha : d310035 p = 1) (hb : d366139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100981 q ha hb
    | true =>
      simp only [d310030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100983 (p : Pattern) (ha : d310041 p = 1) (hb : d366139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100982 q ha hb
    | true =>
      simp only [d310036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100984 (p : Pattern) (ha : d310047 p = 1) (hb : d366139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100983 q ha hb
    | true =>
      simp only [d310042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100985 (p : Pattern) (ha : d310053 p = 1) (hb : d366139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100984 q ha hb
    | true =>
      simp only [d310048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100986 (p : Pattern) (ha : d357440 p = 1) (hb : d366123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366121 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53652 q = 1) (hb : d366122 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d366122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d366122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d357439 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d357440 q = 1) (hb : d366123 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357440, d366123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357440, d366123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro100987 (p : Pattern) (ha : d357556 p = 1) (hb : d366128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d357466 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357467 q = 1) (hb : d366124 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357467, d366124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100986 q ha hb
    | true =>
      simp only [d357467, d366124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d357494 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d357495 q = 1) (hb : d366125 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357495, d366125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357495, d366125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d357523 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d357524 q = 1) (hb : d366126 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357524, d366126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357524, d366126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d357553 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357554 q = 1) (hb : d366127 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d357554, d366127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357554, d366127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d357555 q = 1) (hb : d366128 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d366128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357555, d366128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d366128 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d357556 q = 1) (hb : d366128 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100988 (p : Pattern) (ha : d357562 p = 1) (hb : d366134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357557 q = 1) (hb : d366129 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, d366129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100987 q ha hb
    | true =>
      simp only [d357557, d366129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357558 q = 1) (hb : d366130 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, d366130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, d366130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357559 q = 1) (hb : d366131 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, d366131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357559, d366131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357560 q = 1) (hb : d366132 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d366132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357560, d366132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357561 q = 1) (hb : d366133 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d366133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357561, d366133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357562 q = 1) (hb : d366134 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d366134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357562, d366134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100989 (p : Pattern) (ha : d357568 p = 1) (hb : d366139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357563 q = 1) (hb : d366135 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d366135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100988 q ha hb
    | true =>
      simp only [d357563, d366135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357564 q = 1) (hb : d366136 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d366136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d366136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357565 q = 1) (hb : d366137 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d366137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357565, d366137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357566 q = 1) (hb : d366138 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d366138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357566, d366138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357567 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d366139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357567, d366139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357568 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100990 (p : Pattern) (ha : d357574 p = 1) (hb : d366139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357569 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100989 q ha hb
    | true =>
      simp only [d357569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357570 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357571 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357572 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357573 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357574 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100991 (p : Pattern) (ha : d357580 p = 1) (hb : d366139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357575 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100990 q ha hb
    | true =>
      simp only [d357575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357576 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357577 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357578 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357579 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357580 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100992 (p : Pattern) (ha : d357586 p = 1) (hb : d366139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357581 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100991 q ha hb
    | true =>
      simp only [d357581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357582 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357583 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357584 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357585 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357586 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100993 (p : Pattern) (ha : d357592 p = 1) (hb : d366139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357587 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100992 q ha hb
    | true =>
      simp only [d357587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357588 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357589 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357590 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357591 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357592 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100994 (p : Pattern) (ha : d357598 p = 1) (hb : d366139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357593 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100993 q ha hb
    | true =>
      simp only [d357593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357594 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357595 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357596 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357597 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357598 q = 1) (hb : d366139 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100995 (p : Pattern) (ha : d309843 p = 1) (hb : d366182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366179 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d98 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d99 q = 1) (hb : d366180 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d366180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d366180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d309803 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309804 q = 1) (hb : d366181 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309804, d366181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309804, d366181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d309842 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309843 q = 1) (hb : d366182 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d366182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309843, d366182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro100996 (p : Pattern) (ha : d310011 p = 1) (hb : d366188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d309882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309883 q = 1) (hb : d366183 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309883, d366183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100995 q ha hb
    | true =>
      simp only [d309883, d366183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309923 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309924 q = 1) (hb : d366184 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309924, d366184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309924, d366184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d309965 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309966 q = 1) (hb : d366185 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d366185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309966, d366185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d310008 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310009 q = 1) (hb : d366186 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d366186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310009, d366186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d310010 q = 1) (hb : d366187 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d366187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d310010, d366187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d310011 q = 1) (hb : d366188 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, d366188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d310011, d366188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100997 (p : Pattern) (ha : d310017 p = 1) (hb : d366194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d366189 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, d366189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100996 q ha hb
    | true =>
      simp only [d310012, d366189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d366190 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d366190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d366190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310014 q = 1) (hb : d366191 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d366191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d366191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310015 q = 1) (hb : d366192 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d366192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310015, d366192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310016 q = 1) (hb : d366193 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d366193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310016, d366193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310017 q = 1) (hb : d366194 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d366194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310017, d366194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100998 (p : Pattern) (ha : d310023 p = 1) (hb : d366199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d366195 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d366195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100997 q ha hb
    | true =>
      simp only [d310018, d366195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d366196 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d366196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d366196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310020 q = 1) (hb : d366197 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d366197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d366197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310021 q = 1) (hb : d366198 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d366198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310021, d366198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310022 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d366199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310022, d366199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310023 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100999 (p : Pattern) (ha : d310029 p = 1) (hb : d366199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100998 q ha hb
    | true =>
      simp only [d310024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
