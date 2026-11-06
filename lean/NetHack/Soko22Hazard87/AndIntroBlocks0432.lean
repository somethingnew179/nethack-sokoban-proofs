import NetHack.Soko22Hazard87.AndIntroBlocks0431
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro108000 (p : Pattern) (ha : d380140 p = 1) (hb : d380454 p = 1) : d380583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380454 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380135 q = 1) (hb : d380454 q = 1) : d380578 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380135, d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107999 q ha hb
    | true =>
      simp only [d380135, d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380136 q = 1) (hb : d380454 q = 1) : d380579 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380136, d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380136, d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380137 q = 1) (hb : d380454 q = 1) : d380580 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380137, d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380137, d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380138 q = 1) (hb : d380454 q = 1) : d380581 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380138, d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380138, d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380139 q = 1) (hb : d380454 q = 1) : d380582 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380139, d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380139, d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380140 q = 1) (hb : d380454 q = 1) : d380583 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380140, d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380140, d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108001 (p : Pattern) (ha : d380146 p = 1) (hb : d380454 p = 1) : d380589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380454 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380141 q = 1) (hb : d380454 q = 1) : d380584 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380141, d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108000 q ha hb
    | true =>
      simp only [d380141, d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380142 q = 1) (hb : d380454 q = 1) : d380585 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380142, d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380142, d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380143 q = 1) (hb : d380454 q = 1) : d380586 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380143, d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380143, d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380144 q = 1) (hb : d380454 q = 1) : d380587 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380144, d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380144, d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380145 q = 1) (hb : d380454 q = 1) : d380588 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380145, d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380145, d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380146 q = 1) (hb : d380454 q = 1) : d380589 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380146, d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380146, d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108002 (p : Pattern) (ha : d380152 p = 1) (hb : d380454 p = 1) : d380595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380454 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380147 q = 1) (hb : d380454 q = 1) : d380590 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380147, d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108001 q ha hb
    | true =>
      simp only [d380147, d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380148 q = 1) (hb : d380454 q = 1) : d380591 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380148, d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380148, d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380149 q = 1) (hb : d380454 q = 1) : d380592 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380149, d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380149, d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380150 q = 1) (hb : d380454 q = 1) : d380593 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380150, d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380150, d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380151 q = 1) (hb : d380454 q = 1) : d380594 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380151, d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380151, d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380152 q = 1) (hb : d380454 q = 1) : d380595 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380152, d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380152, d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108003 (p : Pattern) (ha : d380158 p = 1) (hb : d380454 p = 1) : d380601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380454 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380153 q = 1) (hb : d380454 q = 1) : d380596 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380153, d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108002 q ha hb
    | true =>
      simp only [d380153, d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380154 q = 1) (hb : d380454 q = 1) : d380597 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380154, d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380154, d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380155 q = 1) (hb : d380454 q = 1) : d380598 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380155, d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380155, d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380156 q = 1) (hb : d380454 q = 1) : d380599 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380156, d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380156, d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380157 q = 1) (hb : d380454 q = 1) : d380600 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380157, d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380157, d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380158 q = 1) (hb : d380454 q = 1) : d380601 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380158, d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380158, d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108004 (p : Pattern) (ha : d380455 p = 1) (hb : d380553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d318809 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d318809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d318809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86335 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d318810 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d318810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d318810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d318811 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d318811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d318811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d318812 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d318812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d318812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d318813 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d318813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d318813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d380455 q = 1) (hb : d380553 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d380455, d380553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d380455, d380553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro108005 (p : Pattern) (ha : d380461 p = 1) (hb : d380559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380456 q = 1) (hb : d380554 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380456, d380554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108004 q ha hb
    | true =>
      simp only [d380456, d380554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380457 q = 1) (hb : d380555 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380457, d380555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380457, d380555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380458 q = 1) (hb : d380556 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380458, d380556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380458, d380556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380459 q = 1) (hb : d380557 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380459, d380557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380459, d380557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380460 q = 1) (hb : d380558 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380460, d380558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380460, d380558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380461 q = 1) (hb : d380559 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380461, d380559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380461, d380559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108006 (p : Pattern) (ha : d380467 p = 1) (hb : d380565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380462 q = 1) (hb : d380560 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380462, d380560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108005 q ha hb
    | true =>
      simp only [d380462, d380560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380463 q = 1) (hb : d380561 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380463, d380561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380463, d380561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380464 q = 1) (hb : d380562 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380464, d380562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380464, d380562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380465 q = 1) (hb : d380563 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380465, d380563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380465, d380563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380466 q = 1) (hb : d380564 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380466, d380564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380466, d380564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380467 q = 1) (hb : d380565 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380467, d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380467, d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108007 (p : Pattern) (ha : d380473 p = 1) (hb : d380571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380468 q = 1) (hb : d380566 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380468, d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108006 q ha hb
    | true =>
      simp only [d380468, d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380469 q = 1) (hb : d380567 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380469, d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380469, d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380470 q = 1) (hb : d380568 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380470, d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380470, d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380471 q = 1) (hb : d380569 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380471, d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380471, d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380472 q = 1) (hb : d380570 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380472, d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380472, d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380473 q = 1) (hb : d380571 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380473, d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380473, d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108008 (p : Pattern) (ha : d380479 p = 1) (hb : d380577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380474 q = 1) (hb : d380572 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380474, d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108007 q ha hb
    | true =>
      simp only [d380474, d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380475 q = 1) (hb : d380573 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380475, d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380475, d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380476 q = 1) (hb : d380574 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380476, d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380476, d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380477 q = 1) (hb : d380575 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380477, d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380477, d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380478 q = 1) (hb : d380576 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380478, d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380478, d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380479 q = 1) (hb : d380577 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380479, d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380479, d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108009 (p : Pattern) (ha : d380485 p = 1) (hb : d380583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380480 q = 1) (hb : d380578 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380480, d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108008 q ha hb
    | true =>
      simp only [d380480, d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380481 q = 1) (hb : d380579 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380481, d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380481, d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380482 q = 1) (hb : d380580 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380482, d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380482, d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380483 q = 1) (hb : d380581 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380483, d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380483, d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380484 q = 1) (hb : d380582 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380484, d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380484, d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380485 q = 1) (hb : d380583 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380485, d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380485, d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108010 (p : Pattern) (ha : d380491 p = 1) (hb : d380589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380486 q = 1) (hb : d380584 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380486, d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108009 q ha hb
    | true =>
      simp only [d380486, d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380487 q = 1) (hb : d380585 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380487, d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380487, d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380488 q = 1) (hb : d380586 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380488, d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380488, d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380489 q = 1) (hb : d380587 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380489, d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380489, d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380490 q = 1) (hb : d380588 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380490, d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380490, d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380491 q = 1) (hb : d380589 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380491, d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380491, d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108011 (p : Pattern) (ha : d380497 p = 1) (hb : d380595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380492 q = 1) (hb : d380590 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380492, d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108010 q ha hb
    | true =>
      simp only [d380492, d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380493 q = 1) (hb : d380591 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380493, d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380493, d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380494 q = 1) (hb : d380592 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380494, d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380494, d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380495 q = 1) (hb : d380593 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380495, d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380495, d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380496 q = 1) (hb : d380594 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380496, d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380496, d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380497 q = 1) (hb : d380595 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380497, d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380497, d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108012 (p : Pattern) (ha : d380503 p = 1) (hb : d380601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380498 q = 1) (hb : d380596 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380498, d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108011 q ha hb
    | true =>
      simp only [d380498, d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380499 q = 1) (hb : d380597 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380499, d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380499, d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380500 q = 1) (hb : d380598 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380500, d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380500, d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380501 q = 1) (hb : d380599 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380501, d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380501, d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380502 q = 1) (hb : d380600 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380502, d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380502, d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380503 q = 1) (hb : d380601 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380503, d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380503, d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108013 (p : Pattern) (ha : d380504 p = 1) (hb : d380553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d322039 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86400 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d322040 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d322041 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d322042 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d322043 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d380504 q = 1) (hb : d380553 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d380504, d380553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d380504, d380553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro108014 (p : Pattern) (ha : d380510 p = 1) (hb : d380559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380505 q = 1) (hb : d380554 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380505, d380554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108013 q ha hb
    | true =>
      simp only [d380505, d380554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380506 q = 1) (hb : d380555 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380506, d380555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380506, d380555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380507 q = 1) (hb : d380556 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380507, d380556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380507, d380556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380508 q = 1) (hb : d380557 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380508, d380557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380508, d380557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380509 q = 1) (hb : d380558 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380509, d380558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380509, d380558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380510 q = 1) (hb : d380559 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380510, d380559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380510, d380559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108015 (p : Pattern) (ha : d380516 p = 1) (hb : d380565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380511 q = 1) (hb : d380560 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380511, d380560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108014 q ha hb
    | true =>
      simp only [d380511, d380560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380512 q = 1) (hb : d380561 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380512, d380561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380512, d380561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380513 q = 1) (hb : d380562 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380513, d380562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380513, d380562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380514 q = 1) (hb : d380563 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380514, d380563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380514, d380563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380515 q = 1) (hb : d380564 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380515, d380564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380515, d380564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380516 q = 1) (hb : d380565 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380516, d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380516, d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108016 (p : Pattern) (ha : d380522 p = 1) (hb : d380571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380517 q = 1) (hb : d380566 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380517, d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108015 q ha hb
    | true =>
      simp only [d380517, d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380518 q = 1) (hb : d380567 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380518, d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380518, d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380519 q = 1) (hb : d380568 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380519, d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380519, d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380520 q = 1) (hb : d380569 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380520, d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380520, d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380521 q = 1) (hb : d380570 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380521, d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380521, d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380522 q = 1) (hb : d380571 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380522, d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380522, d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108017 (p : Pattern) (ha : d380528 p = 1) (hb : d380577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380523 q = 1) (hb : d380572 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380523, d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108016 q ha hb
    | true =>
      simp only [d380523, d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380524 q = 1) (hb : d380573 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380524, d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380524, d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380525 q = 1) (hb : d380574 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380525, d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380525, d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380526 q = 1) (hb : d380575 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380526, d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380526, d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380527 q = 1) (hb : d380576 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380527, d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380527, d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380528 q = 1) (hb : d380577 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380528, d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380528, d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108018 (p : Pattern) (ha : d380534 p = 1) (hb : d380583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380529 q = 1) (hb : d380578 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380529, d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108017 q ha hb
    | true =>
      simp only [d380529, d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380530 q = 1) (hb : d380579 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380530, d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380530, d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380531 q = 1) (hb : d380580 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380531, d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380531, d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380532 q = 1) (hb : d380581 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380532, d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380532, d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380533 q = 1) (hb : d380582 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380533, d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380533, d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380534 q = 1) (hb : d380583 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380534, d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380534, d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108019 (p : Pattern) (ha : d380540 p = 1) (hb : d380589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380535 q = 1) (hb : d380584 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380535, d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108018 q ha hb
    | true =>
      simp only [d380535, d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380536 q = 1) (hb : d380585 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380536, d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380536, d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380537 q = 1) (hb : d380586 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380537, d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380537, d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380538 q = 1) (hb : d380587 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380538, d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380538, d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380539 q = 1) (hb : d380588 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380539, d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380539, d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380540 q = 1) (hb : d380589 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380540, d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380540, d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108020 (p : Pattern) (ha : d380546 p = 1) (hb : d380595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380541 q = 1) (hb : d380590 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380541, d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108019 q ha hb
    | true =>
      simp only [d380541, d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380542 q = 1) (hb : d380591 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380542, d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380542, d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380543 q = 1) (hb : d380592 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380543, d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380543, d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380544 q = 1) (hb : d380593 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380544, d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380544, d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380545 q = 1) (hb : d380594 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380545, d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380545, d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380546 q = 1) (hb : d380595 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380546, d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380546, d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108021 (p : Pattern) (ha : d380552 p = 1) (hb : d380601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380547 q = 1) (hb : d380596 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380547, d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108020 q ha hb
    | true =>
      simp only [d380547, d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380548 q = 1) (hb : d380597 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380548, d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380548, d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380549 q = 1) (hb : d380598 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380549, d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380549, d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380550 q = 1) (hb : d380599 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380550, d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380550, d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380551 q = 1) (hb : d380600 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380551, d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380551, d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380552 q = 1) (hb : d380601 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380552, d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380552, d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108022 (p : Pattern) (ha : d380074 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380072 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380608 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380073 q = 1) (hb : d380609 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380073, d380609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d380073, d380609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d380074 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380074, d380610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380074, d380610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro108023 (p : Pattern) (ha : d380080 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380075 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108022 q ha hb
    | true =>
      simp only [d380075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380076 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380077 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380078 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380079 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380080 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108024 (p : Pattern) (ha : d380086 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380081 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108023 q ha hb
    | true =>
      simp only [d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380082 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380083 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380084 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380085 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380086 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108025 (p : Pattern) (ha : d380092 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380087 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108024 q ha hb
    | true =>
      simp only [d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380088 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380089 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380090 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380091 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380092 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108026 (p : Pattern) (ha : d380098 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380093 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108025 q ha hb
    | true =>
      simp only [d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380094 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380095 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380096 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380097 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380098 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108027 (p : Pattern) (ha : d380104 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380099 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108026 q ha hb
    | true =>
      simp only [d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380100 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380101 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380102 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380103 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380104 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108028 (p : Pattern) (ha : d380110 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380105 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108027 q ha hb
    | true =>
      simp only [d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380106 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380107 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380108 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380109 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380110 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108029 (p : Pattern) (ha : d0 p = 1) (hb : d380706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380706 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108030 (p : Pattern) (ha : d380122 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380608 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380121 q = 1) (hb : d380609 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380121, d380609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d380121, d380609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d380122 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380122, d380610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380122, d380610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro108031 (p : Pattern) (ha : d380128 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380123 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108030 q ha hb
    | true =>
      simp only [d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380124 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380125 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380126 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380127 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380128 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108032 (p : Pattern) (ha : d380134 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380129 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108031 q ha hb
    | true =>
      simp only [d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380130 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380131 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380132 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380133 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380134 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108033 (p : Pattern) (ha : d380140 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380135 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108032 q ha hb
    | true =>
      simp only [d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380136 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380137 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380138 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380139 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380140 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108034 (p : Pattern) (ha : d380146 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380141 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108033 q ha hb
    | true =>
      simp only [d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380142 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380143 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380144 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380145 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380146 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108035 (p : Pattern) (ha : d380152 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380147 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108034 q ha hb
    | true =>
      simp only [d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380148 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380149 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380150 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380151 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380152 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108036 (p : Pattern) (ha : d380158 p = 1) (hb : d380610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380153 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108035 q ha hb
    | true =>
      simp only [d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380154 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380155 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380156 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380157 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380158 q = 1) (hb : d380610 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108037 (p : Pattern) (ha : d0 p = 1) (hb : d380658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380658 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108038 (p : Pattern) (ha : d380074 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380072 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380708 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380073 q = 1) (hb : d380709 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380073, d380709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d380073, d380709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d380074 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380074, d380710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380074, d380710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro108039 (p : Pattern) (ha : d380080 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380075 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108038 q ha hb
    | true =>
      simp only [d380075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380076 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380077 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380078 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380079 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380080 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108040 (p : Pattern) (ha : d380086 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380081 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108039 q ha hb
    | true =>
      simp only [d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380082 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380083 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380084 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380085 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380086 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108041 (p : Pattern) (ha : d380092 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380087 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108040 q ha hb
    | true =>
      simp only [d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380088 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380089 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380090 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380091 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380092 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108042 (p : Pattern) (ha : d380098 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380093 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108041 q ha hb
    | true =>
      simp only [d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380094 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380095 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380096 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380097 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380098 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108043 (p : Pattern) (ha : d380104 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380099 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108042 q ha hb
    | true =>
      simp only [d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380100 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380101 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380102 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380103 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380104 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108044 (p : Pattern) (ha : d380110 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380105 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108043 q ha hb
    | true =>
      simp only [d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380106 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380107 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380108 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380109 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380110 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108045 (p : Pattern) (ha : d380122 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380708 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380121 q = 1) (hb : d380709 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380121, d380709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d380121, d380709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d380122 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380122, d380710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380122, d380710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro108046 (p : Pattern) (ha : d380128 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380123 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108045 q ha hb
    | true =>
      simp only [d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380124 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380125 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380126 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380127 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380128 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108047 (p : Pattern) (ha : d380134 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380129 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108046 q ha hb
    | true =>
      simp only [d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380130 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380131 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380132 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380133 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380134 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108048 (p : Pattern) (ha : d380140 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380135 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108047 q ha hb
    | true =>
      simp only [d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380136 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380137 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380138 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380139 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380140 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108049 (p : Pattern) (ha : d380146 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380141 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108048 q ha hb
    | true =>
      simp only [d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380142 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380143 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380144 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380145 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380146 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108050 (p : Pattern) (ha : d380152 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380147 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108049 q ha hb
    | true =>
      simp only [d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380148 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380149 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380150 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380151 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380152 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108051 (p : Pattern) (ha : d380158 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380153 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108050 q ha hb
    | true =>
      simp only [d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380154 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380155 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380156 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380157 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380158 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108052 (p : Pattern) (ha : d380014 p = 1) (hb : d380110 p = 1) : d380110 p = 1 := by
  have h0 (q : Pattern) (ha : d380014 q = 1) (hb : d380110 q = 1) : d380110 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro108053 (p : Pattern) (ha : d379588 p = 1) (hb : d380068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319210 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319211 q = 1) (hb : d380063 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d380063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104963 q ha hb
    | true =>
      simp only [d319211, d380063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d379584 q = 1) (hb : d380064 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d379584, d380064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379584, d380064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d379585 q = 1) (hb : d380065 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379585, d380065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379585, d380065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d379586 q = 1) (hb : d380066 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379586, d380066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379586, d380066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d379587 q = 1) (hb : d380067 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379587, d380067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379587, d380067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d379588 q = 1) (hb : d380068 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379588, d380068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379588, d380068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h7 p ha hb
theorem andIntro108054 (p : Pattern) (ha : d379594 p = 1) (hb : d380074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379589 q = 1) (hb : d380069 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379589, d380069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108053 q ha hb
    | true =>
      simp only [d379589, d380069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379590 q = 1) (hb : d380070 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379590, d380070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379590, d380070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379591 q = 1) (hb : d380071 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379591, d380071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379591, d380071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379592 q = 1) (hb : d380072 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379592, d380072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379592, d380072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379593 q = 1) (hb : d380073 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379593, d380073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379593, d380073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379594 q = 1) (hb : d380074 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379594, d380074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379594, d380074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108055 (p : Pattern) (ha : d379600 p = 1) (hb : d380080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379595 q = 1) (hb : d380075 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379595, d380075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108054 q ha hb
    | true =>
      simp only [d379595, d380075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379596 q = 1) (hb : d380076 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379596, d380076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379596, d380076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379597 q = 1) (hb : d380077 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379597, d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379597, d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379598 q = 1) (hb : d380078 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379598, d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379598, d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379599 q = 1) (hb : d380079 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379599, d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379599, d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379600 q = 1) (hb : d380080 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379600, d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379600, d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108056 (p : Pattern) (ha : d379606 p = 1) (hb : d380086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379601 q = 1) (hb : d380081 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379601, d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108055 q ha hb
    | true =>
      simp only [d379601, d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379602 q = 1) (hb : d380082 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379602, d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379602, d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379603 q = 1) (hb : d380083 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379603, d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379603, d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379604 q = 1) (hb : d380084 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379604, d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379604, d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379605 q = 1) (hb : d380085 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379605, d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379605, d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379606 q = 1) (hb : d380086 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379606, d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379606, d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108057 (p : Pattern) (ha : d379612 p = 1) (hb : d380092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379607 q = 1) (hb : d380087 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379607, d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108056 q ha hb
    | true =>
      simp only [d379607, d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379608 q = 1) (hb : d380088 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379608, d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379608, d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379609 q = 1) (hb : d380089 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379609, d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379609, d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379610 q = 1) (hb : d380090 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379610, d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379610, d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379611 q = 1) (hb : d380091 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379611, d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379611, d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379612 q = 1) (hb : d380092 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379612, d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379612, d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108058 (p : Pattern) (ha : d379618 p = 1) (hb : d380098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379613 q = 1) (hb : d380093 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379613, d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108057 q ha hb
    | true =>
      simp only [d379613, d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379614 q = 1) (hb : d380094 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379614, d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379614, d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379615 q = 1) (hb : d380095 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379615, d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379615, d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379616 q = 1) (hb : d380096 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379616, d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379616, d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379617 q = 1) (hb : d380097 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379617, d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379617, d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379618 q = 1) (hb : d380098 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379618, d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379618, d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108059 (p : Pattern) (ha : d379624 p = 1) (hb : d380104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379619 q = 1) (hb : d380099 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379619, d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108058 q ha hb
    | true =>
      simp only [d379619, d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379620 q = 1) (hb : d380100 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379620, d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379620, d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379621 q = 1) (hb : d380101 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379621, d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379621, d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379622 q = 1) (hb : d380102 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379622, d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379622, d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379623 q = 1) (hb : d380103 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379623, d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379623, d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379624 q = 1) (hb : d380104 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379624, d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379624, d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108060 (p : Pattern) (ha : d379630 p = 1) (hb : d380110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379625 q = 1) (hb : d380105 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379625, d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108059 q ha hb
    | true =>
      simp only [d379625, d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379626 q = 1) (hb : d380106 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379626, d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379626, d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379627 q = 1) (hb : d380107 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379627, d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379627, d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379628 q = 1) (hb : d380108 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379628, d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379628, d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379629 q = 1) (hb : d380109 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379629, d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379629, d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379630 q = 1) (hb : d380110 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379630, d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379630, d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108061 (p : Pattern) (ha : d380014 p = 1) (hb : d380158 p = 1) : d380158 p = 1 := by
  have h0 (q : Pattern) (ha : d380014 q = 1) (hb : d380158 q = 1) : d380158 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro108062 (p : Pattern) (ha : d379588 p = 1) (hb : d380116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319210 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319211 q = 1) (hb : d380111 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d380111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105138 q ha hb
    | true =>
      simp only [d319211, d380111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d379584 q = 1) (hb : d380112 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d379584, d380112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379584, d380112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d379585 q = 1) (hb : d380113 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379585, d380113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379585, d380113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d379586 q = 1) (hb : d380114 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379586, d380114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379586, d380114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d379587 q = 1) (hb : d380115 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379587, d380115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379587, d380115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d379588 q = 1) (hb : d380116 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379588, d380116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379588, d380116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h7 p ha hb
theorem andIntro108063 (p : Pattern) (ha : d379594 p = 1) (hb : d380122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379589 q = 1) (hb : d380117 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379589, d380117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108062 q ha hb
    | true =>
      simp only [d379589, d380117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379590 q = 1) (hb : d380118 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379590, d380118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379590, d380118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379591 q = 1) (hb : d380119 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379591, d380119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379591, d380119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379592 q = 1) (hb : d380120 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379592, d380120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379592, d380120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379593 q = 1) (hb : d380121 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379593, d380121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379593, d380121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379594 q = 1) (hb : d380122 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379594, d380122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379594, d380122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108064 (p : Pattern) (ha : d379600 p = 1) (hb : d380128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379595 q = 1) (hb : d380123 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379595, d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108063 q ha hb
    | true =>
      simp only [d379595, d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379596 q = 1) (hb : d380124 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379596, d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379596, d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379597 q = 1) (hb : d380125 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379597, d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379597, d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379598 q = 1) (hb : d380126 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379598, d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379598, d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379599 q = 1) (hb : d380127 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379599, d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379599, d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379600 q = 1) (hb : d380128 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379600, d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379600, d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108065 (p : Pattern) (ha : d379606 p = 1) (hb : d380134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379601 q = 1) (hb : d380129 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379601, d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108064 q ha hb
    | true =>
      simp only [d379601, d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379602 q = 1) (hb : d380130 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379602, d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379602, d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379603 q = 1) (hb : d380131 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379603, d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379603, d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379604 q = 1) (hb : d380132 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379604, d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379604, d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379605 q = 1) (hb : d380133 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379605, d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379605, d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379606 q = 1) (hb : d380134 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379606, d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379606, d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108066 (p : Pattern) (ha : d379612 p = 1) (hb : d380140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379607 q = 1) (hb : d380135 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379607, d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108065 q ha hb
    | true =>
      simp only [d379607, d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379608 q = 1) (hb : d380136 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379608, d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379608, d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379609 q = 1) (hb : d380137 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379609, d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379609, d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379610 q = 1) (hb : d380138 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379610, d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379610, d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379611 q = 1) (hb : d380139 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379611, d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379611, d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379612 q = 1) (hb : d380140 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379612, d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379612, d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108067 (p : Pattern) (ha : d379618 p = 1) (hb : d380146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379613 q = 1) (hb : d380141 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379613, d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108066 q ha hb
    | true =>
      simp only [d379613, d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379614 q = 1) (hb : d380142 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379614, d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379614, d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379615 q = 1) (hb : d380143 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379615, d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379615, d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379616 q = 1) (hb : d380144 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379616, d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379616, d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379617 q = 1) (hb : d380145 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379617, d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379617, d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379618 q = 1) (hb : d380146 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379618, d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379618, d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108068 (p : Pattern) (ha : d379624 p = 1) (hb : d380152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379619 q = 1) (hb : d380147 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379619, d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108067 q ha hb
    | true =>
      simp only [d379619, d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379620 q = 1) (hb : d380148 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379620, d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379620, d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379621 q = 1) (hb : d380149 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379621, d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379621, d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379622 q = 1) (hb : d380150 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379622, d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379622, d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379623 q = 1) (hb : d380151 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379623, d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379623, d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379624 q = 1) (hb : d380152 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379624, d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379624, d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108069 (p : Pattern) (ha : d379630 p = 1) (hb : d380158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379625 q = 1) (hb : d380153 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379625, d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108068 q ha hb
    | true =>
      simp only [d379625, d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379626 q = 1) (hb : d380154 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379626, d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379626, d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379627 q = 1) (hb : d380155 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379627, d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379627, d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379628 q = 1) (hb : d380156 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379628, d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379628, d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379629 q = 1) (hb : d380157 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379629, d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379629, d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379630 q = 1) (hb : d380158 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379630, d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379630, d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108070 (p : Pattern) (ha : d379635 p = 1) (hb : d380116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322121 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322122 q = 1) (hb : d380111 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322122, d380111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105170 q ha hb
    | true =>
      simp only [d322122, d380111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d379631 q = 1) (hb : d380112 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d379631, d380112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379631, d380112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379632 q = 1) (hb : d380113 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379632, d380113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379632, d380113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d379633 q = 1) (hb : d380114 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379633, d380114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379633, d380114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d379634 q = 1) (hb : d380115 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379634, d380115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379634, d380115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d379635 q = 1) (hb : d380116 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379635, d380116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379635, d380116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro108071 (p : Pattern) (ha : d379641 p = 1) (hb : d380122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379636 q = 1) (hb : d380117 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379636, d380117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108070 q ha hb
    | true =>
      simp only [d379636, d380117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379637 q = 1) (hb : d380118 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379637, d380118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379637, d380118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379638 q = 1) (hb : d380119 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379638, d380119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379638, d380119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379639 q = 1) (hb : d380120 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379639, d380120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379639, d380120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379640 q = 1) (hb : d380121 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379640, d380121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379640, d380121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379641 q = 1) (hb : d380122 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379641, d380122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379641, d380122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108072 (p : Pattern) (ha : d379647 p = 1) (hb : d380128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379642 q = 1) (hb : d380123 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379642, d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108071 q ha hb
    | true =>
      simp only [d379642, d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379643 q = 1) (hb : d380124 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379643, d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379643, d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379644 q = 1) (hb : d380125 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379644, d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379644, d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379645 q = 1) (hb : d380126 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379645, d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379645, d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379646 q = 1) (hb : d380127 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379646, d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379646, d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379647 q = 1) (hb : d380128 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379647, d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379647, d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108073 (p : Pattern) (ha : d379653 p = 1) (hb : d380134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379648 q = 1) (hb : d380129 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379648, d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108072 q ha hb
    | true =>
      simp only [d379648, d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379649 q = 1) (hb : d380130 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379649, d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379649, d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379650 q = 1) (hb : d380131 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379650, d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379650, d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379651 q = 1) (hb : d380132 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379651, d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379651, d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379652 q = 1) (hb : d380133 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379652, d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379652, d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379653 q = 1) (hb : d380134 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379653, d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379653, d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108074 (p : Pattern) (ha : d379659 p = 1) (hb : d380140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379654 q = 1) (hb : d380135 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379654, d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108073 q ha hb
    | true =>
      simp only [d379654, d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379655 q = 1) (hb : d380136 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379655, d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379655, d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379656 q = 1) (hb : d380137 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379656, d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379656, d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379657 q = 1) (hb : d380138 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379657, d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379657, d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379658 q = 1) (hb : d380139 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379658, d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379658, d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379659 q = 1) (hb : d380140 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379659, d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379659, d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108075 (p : Pattern) (ha : d379665 p = 1) (hb : d380146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379660 q = 1) (hb : d380141 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379660, d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108074 q ha hb
    | true =>
      simp only [d379660, d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379661 q = 1) (hb : d380142 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379661, d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379661, d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379662 q = 1) (hb : d380143 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379662, d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379662, d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379663 q = 1) (hb : d380144 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379663, d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379663, d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379664 q = 1) (hb : d380145 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379664, d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379664, d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379665 q = 1) (hb : d380146 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379665, d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379665, d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108076 (p : Pattern) (ha : d379671 p = 1) (hb : d380152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379666 q = 1) (hb : d380147 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379666, d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108075 q ha hb
    | true =>
      simp only [d379666, d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379667 q = 1) (hb : d380148 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379667, d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379667, d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379668 q = 1) (hb : d380149 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379668, d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379668, d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379669 q = 1) (hb : d380150 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379669, d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379669, d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379670 q = 1) (hb : d380151 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379670, d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379670, d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379671 q = 1) (hb : d380152 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379671, d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379671, d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108077 (p : Pattern) (ha : d379677 p = 1) (hb : d380158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379672 q = 1) (hb : d380153 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379672, d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108076 q ha hb
    | true =>
      simp only [d379672, d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379673 q = 1) (hb : d380154 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379673, d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379673, d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379674 q = 1) (hb : d380155 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379674, d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379674, d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379675 q = 1) (hb : d380156 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379675, d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379675, d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379676 q = 1) (hb : d380157 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379676, d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379676, d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379677 q = 1) (hb : d380158 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379677, d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379677, d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108078 (p : Pattern) (ha : d380080 p = 1) (hb : d380717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380074 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380715 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380075 q = 1) (hb : d380716 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380075, d380716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d380075, d380716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d380076 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380076, d380717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380076, d380717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d380077 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d380078 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d380079 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d380080 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro108079 (p : Pattern) (ha : d380086 p = 1) (hb : d380717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380081 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108078 q ha hb
    | true =>
      simp only [d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380082 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380083 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380084 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380085 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380086 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108080 (p : Pattern) (ha : d380092 p = 1) (hb : d380717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380087 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108079 q ha hb
    | true =>
      simp only [d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380088 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380089 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380090 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380091 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380092 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108081 (p : Pattern) (ha : d380098 p = 1) (hb : d380717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380093 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108080 q ha hb
    | true =>
      simp only [d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380094 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380095 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380096 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380097 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380098 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108082 (p : Pattern) (ha : d380104 p = 1) (hb : d380717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380099 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108081 q ha hb
    | true =>
      simp only [d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380100 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380101 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380102 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380103 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380104 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108083 (p : Pattern) (ha : d380110 p = 1) (hb : d380717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380105 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108082 q ha hb
    | true =>
      simp only [d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380106 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380107 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380108 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380109 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380110 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108084 (p : Pattern) (ha : d0 p = 1) (hb : d380805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380805 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108085 (p : Pattern) (ha : d380128 p = 1) (hb : d380717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380122 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380715 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380123 q = 1) (hb : d380716 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380123, d380716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d380123, d380716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d380124 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380124, d380717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380124, d380717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d380125 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d380126 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d380127 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d380128 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro108086 (p : Pattern) (ha : d380134 p = 1) (hb : d380717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380129 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108085 q ha hb
    | true =>
      simp only [d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380130 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380131 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380132 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380133 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380134 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108087 (p : Pattern) (ha : d380140 p = 1) (hb : d380717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380135 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108086 q ha hb
    | true =>
      simp only [d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380136 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380137 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380138 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380139 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380140 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108088 (p : Pattern) (ha : d380146 p = 1) (hb : d380717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380141 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108087 q ha hb
    | true =>
      simp only [d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380142 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380143 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380144 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380145 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380146 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108089 (p : Pattern) (ha : d380152 p = 1) (hb : d380717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380147 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108088 q ha hb
    | true =>
      simp only [d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380148 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380149 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380150 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380151 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380152 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108090 (p : Pattern) (ha : d380158 p = 1) (hb : d380717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380153 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108089 q ha hb
    | true =>
      simp only [d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380154 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380155 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380156 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380157 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380158 q = 1) (hb : d380717 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108091 (p : Pattern) (ha : d0 p = 1) (hb : d380849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380849 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108092 (p : Pattern) (ha : d379875 p = 1) (hb : d380080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380074 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379873 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379874 q = 1) (hb : d380075 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379874, d380075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d379874, d380075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379875 q = 1) (hb : d380076 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379875, d380076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379875, d380076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379875 q = 1) (hb : d380077 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d379875 q = 1) (hb : d380078 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d379875 q = 1) (hb : d380079 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d379875 q = 1) (hb : d380080 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro108093 (p : Pattern) (ha : d379875 p = 1) (hb : d380086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379875 q = 1) (hb : d380081 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108092 q ha hb
    | true =>
      simp only [d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379875 q = 1) (hb : d380082 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379875 q = 1) (hb : d380083 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379875 q = 1) (hb : d380084 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379875 q = 1) (hb : d380085 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379875 q = 1) (hb : d380086 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108094 (p : Pattern) (ha : d379875 p = 1) (hb : d380092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379875 q = 1) (hb : d380087 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108093 q ha hb
    | true =>
      simp only [d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379875 q = 1) (hb : d380088 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379875 q = 1) (hb : d380089 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379875 q = 1) (hb : d380090 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379875 q = 1) (hb : d380091 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379875 q = 1) (hb : d380092 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108095 (p : Pattern) (ha : d379875 p = 1) (hb : d380098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379875 q = 1) (hb : d380093 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108094 q ha hb
    | true =>
      simp only [d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379875 q = 1) (hb : d380094 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379875 q = 1) (hb : d380095 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379875 q = 1) (hb : d380096 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379875 q = 1) (hb : d380097 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379875 q = 1) (hb : d380098 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108096 (p : Pattern) (ha : d379875 p = 1) (hb : d380104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379875 q = 1) (hb : d380099 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108095 q ha hb
    | true =>
      simp only [d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379875 q = 1) (hb : d380100 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379875 q = 1) (hb : d380101 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379875 q = 1) (hb : d380102 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379875 q = 1) (hb : d380103 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379875 q = 1) (hb : d380104 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108097 (p : Pattern) (ha : d379875 p = 1) (hb : d380110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379875 q = 1) (hb : d380105 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108096 q ha hb
    | true =>
      simp only [d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379875 q = 1) (hb : d380106 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379875 q = 1) (hb : d380107 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379875 q = 1) (hb : d380108 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379875 q = 1) (hb : d380109 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379875 q = 1) (hb : d380110 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108098 (p : Pattern) (ha : d379875 p = 1) (hb : d380128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380122 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379873 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379874 q = 1) (hb : d380123 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379874, d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d379874, d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379875 q = 1) (hb : d380124 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379875, d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379875, d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379875 q = 1) (hb : d380125 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d379875 q = 1) (hb : d380126 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d379875 q = 1) (hb : d380127 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d379875 q = 1) (hb : d380128 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro108099 (p : Pattern) (ha : d379875 p = 1) (hb : d380134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379875 q = 1) (hb : d380129 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108098 q ha hb
    | true =>
      simp only [d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379875 q = 1) (hb : d380130 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379875 q = 1) (hb : d380131 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379875 q = 1) (hb : d380132 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379875 q = 1) (hb : d380133 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379875 q = 1) (hb : d380134 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108100 (p : Pattern) (ha : d379875 p = 1) (hb : d380140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379875 q = 1) (hb : d380135 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108099 q ha hb
    | true =>
      simp only [d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379875 q = 1) (hb : d380136 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379875 q = 1) (hb : d380137 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379875 q = 1) (hb : d380138 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379875 q = 1) (hb : d380139 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379875 q = 1) (hb : d380140 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108101 (p : Pattern) (ha : d379875 p = 1) (hb : d380146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379875 q = 1) (hb : d380141 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108100 q ha hb
    | true =>
      simp only [d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379875 q = 1) (hb : d380142 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379875 q = 1) (hb : d380143 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379875 q = 1) (hb : d380144 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379875 q = 1) (hb : d380145 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379875 q = 1) (hb : d380146 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108102 (p : Pattern) (ha : d379875 p = 1) (hb : d380152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379875 q = 1) (hb : d380147 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108101 q ha hb
    | true =>
      simp only [d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379875 q = 1) (hb : d380148 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379875 q = 1) (hb : d380149 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379875 q = 1) (hb : d380150 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379875 q = 1) (hb : d380151 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379875 q = 1) (hb : d380152 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108103 (p : Pattern) (ha : d379875 p = 1) (hb : d380158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379875 q = 1) (hb : d380153 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108102 q ha hb
    | true =>
      simp only [d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379875 q = 1) (hb : d380154 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379875 q = 1) (hb : d380155 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379875 q = 1) (hb : d380156 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379875 q = 1) (hb : d380157 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379875 q = 1) (hb : d380158 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108104 (p : Pattern) (ha : d380504 p = 1) (hb : d380853 p = 1) : d47563 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d99 q = 1) : d99 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d322042 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322043 q = 1) (hb : d365990 q = 1) : d47562 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d322043, d365990, d47562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322043, d365990, d47562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d380504 q = 1) (hb : d380853 q = 1) : d47563 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d380504, d380853, d47563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380504, d380853, d47563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro108105 (p : Pattern) (ha : d380510 p = 1) (hb : d380853 p = 1) : d47569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380505 q = 1) (hb : d380853 q = 1) : d47564 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380505, d47564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108104 q ha hb
    | true =>
      simp only [d380505, d47564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380506 q = 1) (hb : d380853 q = 1) : d47565 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380506, d47565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380506, d47565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380507 q = 1) (hb : d380853 q = 1) : d47566 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380507, d47566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380507, d47566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380508 q = 1) (hb : d380853 q = 1) : d47567 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380508, d47567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380508, d47567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380509 q = 1) (hb : d380853 q = 1) : d47568 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380509, d47568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380509, d47568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380510 q = 1) (hb : d380853 q = 1) : d47569 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380510, d47569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380510, d47569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108106 (p : Pattern) (ha : d380516 p = 1) (hb : d380855 p = 1) : d47575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380511 q = 1) (hb : d380853 q = 1) : d47570 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380511, d47570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108105 q ha hb
    | true =>
      simp only [d380511, d47570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380512 q = 1) (hb : d380853 q = 1) : d47571 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380512, d47571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380512, d47571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380513 q = 1) (hb : d380853 q = 1) : d47572 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380513, d47572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380513, d47572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d380514 q = 1) (hb : d380854 q = 1) : d47573 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380514, d380854, d47573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380514, d380854, d47573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d380515 q = 1) (hb : d380855 q = 1) : d47574 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380515, d380855, d47574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380515, d380855, d47574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d380516 q = 1) (hb : d380855 q = 1) : d47575 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380516, d47575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380516, d47575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro108107 (p : Pattern) (ha : d380522 p = 1) (hb : d380855 p = 1) : d47581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380517 q = 1) (hb : d380855 q = 1) : d47576 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380517, d47576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108106 q ha hb
    | true =>
      simp only [d380517, d47576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380518 q = 1) (hb : d380855 q = 1) : d47577 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380518, d47577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380518, d47577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380519 q = 1) (hb : d380855 q = 1) : d47578 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380519, d47578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380519, d47578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380520 q = 1) (hb : d380855 q = 1) : d47579 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380520, d47579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380520, d47579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380521 q = 1) (hb : d380855 q = 1) : d47580 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380521, d47580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380521, d47580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380522 q = 1) (hb : d380855 q = 1) : d47581 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380522, d47581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380522, d47581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108108 (p : Pattern) (ha : d380528 p = 1) (hb : d380855 p = 1) : d47587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380523 q = 1) (hb : d380855 q = 1) : d47582 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380523, d47582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108107 q ha hb
    | true =>
      simp only [d380523, d47582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380524 q = 1) (hb : d380855 q = 1) : d47583 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380524, d47583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380524, d47583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380525 q = 1) (hb : d380855 q = 1) : d47584 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380525, d47584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380525, d47584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380526 q = 1) (hb : d380855 q = 1) : d47585 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380526, d47585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380526, d47585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380527 q = 1) (hb : d380855 q = 1) : d47586 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380527, d47586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380527, d47586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380528 q = 1) (hb : d380855 q = 1) : d47587 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380528, d47587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380528, d47587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108109 (p : Pattern) (ha : d380534 p = 1) (hb : d380855 p = 1) : d47593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380529 q = 1) (hb : d380855 q = 1) : d47588 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380529, d47588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108108 q ha hb
    | true =>
      simp only [d380529, d47588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380530 q = 1) (hb : d380855 q = 1) : d47589 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380530, d47589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380530, d47589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380531 q = 1) (hb : d380855 q = 1) : d47590 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380531, d47590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380531, d47590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380532 q = 1) (hb : d380855 q = 1) : d47591 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380532, d47591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380532, d47591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380533 q = 1) (hb : d380855 q = 1) : d47592 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380533, d47592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380533, d47592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380534 q = 1) (hb : d380855 q = 1) : d47593 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380534, d47593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380534, d47593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108110 (p : Pattern) (ha : d380540 p = 1) (hb : d380855 p = 1) : d47599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380535 q = 1) (hb : d380855 q = 1) : d47594 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380535, d47594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108109 q ha hb
    | true =>
      simp only [d380535, d47594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380536 q = 1) (hb : d380855 q = 1) : d47595 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380536, d47595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380536, d47595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380537 q = 1) (hb : d380855 q = 1) : d47596 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380537, d47596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380537, d47596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380538 q = 1) (hb : d380855 q = 1) : d47597 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380538, d47597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380538, d47597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380539 q = 1) (hb : d380855 q = 1) : d47598 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380539, d47598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380539, d47598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380540 q = 1) (hb : d380855 q = 1) : d47599 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380540, d47599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380540, d47599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108111 (p : Pattern) (ha : d380546 p = 1) (hb : d380855 p = 1) : d47605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380541 q = 1) (hb : d380855 q = 1) : d47600 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380541, d47600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108110 q ha hb
    | true =>
      simp only [d380541, d47600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380542 q = 1) (hb : d380855 q = 1) : d47601 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380542, d47601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380542, d47601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380543 q = 1) (hb : d380855 q = 1) : d47602 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380543, d47602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380543, d47602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380544 q = 1) (hb : d380855 q = 1) : d47603 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380544, d47603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380544, d47603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380545 q = 1) (hb : d380855 q = 1) : d47604 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380545, d47604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380545, d47604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380546 q = 1) (hb : d380855 q = 1) : d47605 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380546, d47605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380546, d47605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108112 (p : Pattern) (ha : d380552 p = 1) (hb : d380855 p = 1) : d47611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380547 q = 1) (hb : d380855 q = 1) : d47606 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380547, d47606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108111 q ha hb
    | true =>
      simp only [d380547, d47606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380548 q = 1) (hb : d380855 q = 1) : d47607 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380548, d47607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380548, d47607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380549 q = 1) (hb : d380855 q = 1) : d47608 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380549, d47608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380549, d47608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380550 q = 1) (hb : d380855 q = 1) : d47609 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380550, d47609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380550, d47609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380551 q = 1) (hb : d380855 q = 1) : d47610 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380551, d47610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380551, d47610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380552 q = 1) (hb : d380855 q = 1) : d47611 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380552, d47611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380552, d47611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108113 (p : Pattern) (ha : d47563 p = 1) (hb : d380857 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d47562 q = 1) (hb : d380856 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d47562, d380856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47562, d380856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47563 q = 1) (hb : d380857 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d47563, d380857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47563, d380857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108114 (p : Pattern) (ha : d47569 p = 1) (hb : d380863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47564 q = 1) (hb : d380858 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47564, d380858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108113 q ha hb
    | true =>
      simp only [d47564, d380858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47565 q = 1) (hb : d380859 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47565, d380859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47565, d380859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47566 q = 1) (hb : d380860 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47566, d380860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47566, d380860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47567 q = 1) (hb : d380861 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47567, d380861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47567, d380861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47568 q = 1) (hb : d380862 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47568, d380862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47568, d380862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47569 q = 1) (hb : d380863 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47569, d380863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47569, d380863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108115 (p : Pattern) (ha : d47575 p = 1) (hb : d380869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47570 q = 1) (hb : d380864 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47570, d380864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108114 q ha hb
    | true =>
      simp only [d47570, d380864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47571 q = 1) (hb : d380865 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47571, d380865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47571, d380865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47572 q = 1) (hb : d380866 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47572, d380866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47572, d380866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47573 q = 1) (hb : d380867 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47573, d380867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47573, d380867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47574 q = 1) (hb : d380868 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47574, d380868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47574, d380868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47575 q = 1) (hb : d380869 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47575, d380869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47575, d380869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108116 (p : Pattern) (ha : d47581 p = 1) (hb : d380875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47576 q = 1) (hb : d380870 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47576, d380870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108115 q ha hb
    | true =>
      simp only [d47576, d380870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47577 q = 1) (hb : d380871 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47577, d380871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47577, d380871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47578 q = 1) (hb : d380872 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47578, d380872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47578, d380872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47579 q = 1) (hb : d380873 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47579, d380873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47579, d380873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47580 q = 1) (hb : d380874 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47580, d380874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47580, d380874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47581 q = 1) (hb : d380875 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47581, d380875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47581, d380875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108117 (p : Pattern) (ha : d47587 p = 1) (hb : d380881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47582 q = 1) (hb : d380876 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47582, d380876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108116 q ha hb
    | true =>
      simp only [d47582, d380876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47583 q = 1) (hb : d380877 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47583, d380877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47583, d380877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47584 q = 1) (hb : d380878 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47584, d380878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47584, d380878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47585 q = 1) (hb : d380879 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47585, d380879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47585, d380879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47586 q = 1) (hb : d380880 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47586, d380880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47586, d380880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47587 q = 1) (hb : d380881 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47587, d380881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47587, d380881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108118 (p : Pattern) (ha : d47593 p = 1) (hb : d380887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47588 q = 1) (hb : d380882 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47588, d380882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108117 q ha hb
    | true =>
      simp only [d47588, d380882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47589 q = 1) (hb : d380883 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47589, d380883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47589, d380883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47590 q = 1) (hb : d380884 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47590, d380884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47590, d380884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47591 q = 1) (hb : d380885 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47591, d380885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47591, d380885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47592 q = 1) (hb : d380886 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47592, d380886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47592, d380886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47593 q = 1) (hb : d380887 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47593, d380887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47593, d380887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108119 (p : Pattern) (ha : d47599 p = 1) (hb : d380893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47594 q = 1) (hb : d380888 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47594, d380888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108118 q ha hb
    | true =>
      simp only [d47594, d380888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47595 q = 1) (hb : d380889 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47595, d380889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47595, d380889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47596 q = 1) (hb : d380890 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47596, d380890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47596, d380890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47597 q = 1) (hb : d380891 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47597, d380891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47597, d380891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47598 q = 1) (hb : d380892 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47598, d380892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47598, d380892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47599 q = 1) (hb : d380893 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47599, d380893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47599, d380893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108120 (p : Pattern) (ha : d47605 p = 1) (hb : d380899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47600 q = 1) (hb : d380894 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47600, d380894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108119 q ha hb
    | true =>
      simp only [d47600, d380894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47601 q = 1) (hb : d380895 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47601, d380895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47601, d380895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47602 q = 1) (hb : d380896 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47602, d380896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47602, d380896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47603 q = 1) (hb : d380897 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47603, d380897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47603, d380897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47604 q = 1) (hb : d380898 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47604, d380898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47604, d380898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47605 q = 1) (hb : d380899 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47605, d380899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47605, d380899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108121 (p : Pattern) (ha : d47611 p = 1) (hb : d380905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47606 q = 1) (hb : d380900 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47606, d380900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108120 q ha hb
    | true =>
      simp only [d47606, d380900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47607 q = 1) (hb : d380901 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47607, d380901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47607, d380901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47608 q = 1) (hb : d380902 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47608, d380902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47608, d380902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47609 q = 1) (hb : d380903 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47609, d380903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47609, d380903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47610 q = 1) (hb : d380904 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47610, d380904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47610, d380904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47611 q = 1) (hb : d380905 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47611, d380905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47611, d380905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108122 (p : Pattern) (ha : d380553 p = 1) (hb : d380853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53652 q = 1) (hb : d365990 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d365990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d365990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d380553 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d380553, d380853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380553, d380853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro108123 (p : Pattern) (ha : d380559 p = 1) (hb : d380853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380554 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108122 q ha hb
    | true =>
      simp only [d380554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380555 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380556 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380557 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380558 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380559 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108124 (p : Pattern) (ha : d380565 p = 1) (hb : d380855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380560 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108123 q ha hb
    | true =>
      simp only [d380560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380561 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380562 q = 1) (hb : d380853 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d380563 q = 1) (hb : d380854 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380563, d380854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380563, d380854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d380564 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380564, d380855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380564, d380855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d380565 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro108125 (p : Pattern) (ha : d380571 p = 1) (hb : d380855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380566 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108124 q ha hb
    | true =>
      simp only [d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380567 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380568 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380569 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380570 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380571 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108126 (p : Pattern) (ha : d380577 p = 1) (hb : d380855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380572 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108125 q ha hb
    | true =>
      simp only [d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380573 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380574 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380575 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380576 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380577 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108127 (p : Pattern) (ha : d380583 p = 1) (hb : d380855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380578 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108126 q ha hb
    | true =>
      simp only [d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380579 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380580 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380581 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380582 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380583 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108128 (p : Pattern) (ha : d380589 p = 1) (hb : d380855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380584 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108127 q ha hb
    | true =>
      simp only [d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380585 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380586 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380587 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380588 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380589 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108129 (p : Pattern) (ha : d380595 p = 1) (hb : d380855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380590 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108128 q ha hb
    | true =>
      simp only [d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380591 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380592 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380593 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380594 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380595 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108130 (p : Pattern) (ha : d380601 p = 1) (hb : d380855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380596 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108129 q ha hb
    | true =>
      simp only [d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380597 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380598 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380599 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380600 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380601 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108131 (p : Pattern) (ha : d0 p = 1) (hb : d380905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380905 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108132 (p : Pattern) (ha : d0 p = 1) (hb : d47611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d47611 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108133 (p : Pattern) (ha : d380516 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380513 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380912 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380514 q = 1) (hb : d380913 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380514, d380913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d380514, d380913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d380515 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380515, d380914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380515, d380914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d380516 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro108134 (p : Pattern) (ha : d380522 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380517 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108133 q ha hb
    | true =>
      simp only [d380517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380518 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380519 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380520 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380521 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380522 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108135 (p : Pattern) (ha : d380528 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380523 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108134 q ha hb
    | true =>
      simp only [d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380524 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380525 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380526 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380527 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380528 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108136 (p : Pattern) (ha : d380534 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380529 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108135 q ha hb
    | true =>
      simp only [d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380530 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380531 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380532 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380533 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380534 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108137 (p : Pattern) (ha : d380540 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380535 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108136 q ha hb
    | true =>
      simp only [d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380536 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380537 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380538 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380539 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380540 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108138 (p : Pattern) (ha : d380546 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380541 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108137 q ha hb
    | true =>
      simp only [d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380542 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380543 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380544 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380545 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380546 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108139 (p : Pattern) (ha : d380552 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380547 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108138 q ha hb
    | true =>
      simp only [d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380548 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380549 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380550 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380551 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380552 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108140 (p : Pattern) (ha : d380565 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380562 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380912 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380563 q = 1) (hb : d380913 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380563, d380913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d380563, d380913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d380564 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380564, d380914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380564, d380914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d380565 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro108141 (p : Pattern) (ha : d380571 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380566 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108140 q ha hb
    | true =>
      simp only [d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380567 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380568 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380569 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380570 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380571 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108142 (p : Pattern) (ha : d380577 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380572 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108141 q ha hb
    | true =>
      simp only [d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380573 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380574 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380575 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380576 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380577 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108143 (p : Pattern) (ha : d380583 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380578 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108142 q ha hb
    | true =>
      simp only [d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380579 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380580 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380581 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380582 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380583 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108144 (p : Pattern) (ha : d380589 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380584 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108143 q ha hb
    | true =>
      simp only [d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380585 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380586 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380587 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380588 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380589 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108145 (p : Pattern) (ha : d380595 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380590 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108144 q ha hb
    | true =>
      simp only [d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380591 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380592 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380593 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380594 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380595 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108146 (p : Pattern) (ha : d380601 p = 1) (hb : d380914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380596 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108145 q ha hb
    | true =>
      simp only [d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380597 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380598 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380599 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380600 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380601 q = 1) (hb : d380914 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108147 (p : Pattern) (ha : d380516 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380513 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380916 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380514 q = 1) (hb : d380917 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380514, d380917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d380514, d380917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d380515 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380515, d380918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380515, d380918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d380516 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro108148 (p : Pattern) (ha : d380522 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380517 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108147 q ha hb
    | true =>
      simp only [d380517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380518 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380519 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380520 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380521 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380522 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108149 (p : Pattern) (ha : d380528 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380523 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108148 q ha hb
    | true =>
      simp only [d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380524 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380525 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380526 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380527 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380528 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108150 (p : Pattern) (ha : d380534 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380529 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108149 q ha hb
    | true =>
      simp only [d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380530 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380531 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380532 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380533 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380534 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108151 (p : Pattern) (ha : d380540 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380535 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108150 q ha hb
    | true =>
      simp only [d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380536 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380537 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380538 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380539 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380540 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108152 (p : Pattern) (ha : d380546 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380541 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108151 q ha hb
    | true =>
      simp only [d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380542 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380543 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380544 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380545 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380546 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108153 (p : Pattern) (ha : d380552 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380547 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108152 q ha hb
    | true =>
      simp only [d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380548 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380549 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380550 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380551 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380552 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108154 (p : Pattern) (ha : d380565 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380562 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380916 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380563 q = 1) (hb : d380917 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380563, d380917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d380563, d380917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d380564 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380564, d380918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380564, d380918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d380565 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro108155 (p : Pattern) (ha : d380571 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380566 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108154 q ha hb
    | true =>
      simp only [d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380567 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380568 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380569 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380570 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380571 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108156 (p : Pattern) (ha : d380577 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380572 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108155 q ha hb
    | true =>
      simp only [d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380573 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380574 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380575 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380576 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380577 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108157 (p : Pattern) (ha : d380583 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380578 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108156 q ha hb
    | true =>
      simp only [d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380579 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380580 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380581 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380582 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380583 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108158 (p : Pattern) (ha : d380589 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380584 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108157 q ha hb
    | true =>
      simp only [d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380585 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380586 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380587 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380588 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380589 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108159 (p : Pattern) (ha : d380595 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380590 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108158 q ha hb
    | true =>
      simp only [d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380591 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380592 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380593 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380594 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380595 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108160 (p : Pattern) (ha : d380601 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380596 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108159 q ha hb
    | true =>
      simp only [d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380597 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380598 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380599 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380600 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380601 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108161 (p : Pattern) (ha : d380454 p = 1) (hb : d380552 p = 1) : d380552 p = 1 := by
  have h0 (q : Pattern) (ha : d380454 q = 1) (hb : d380552 q = 1) : d380552 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro108162 (p : Pattern) (ha : d318967 p = 1) (hb : d380504 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d318809 q = 1) (hb : d322039 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d318809, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318809, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104937 q ha hb
  have h6 (q : Pattern) (ha : d318810 q = 1) (hb : d322040 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d318810, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318810, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318811 q = 1) (hb : d322041 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d318811, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318811, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318812 q = 1) (hb : d322042 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d318812, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318812, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318813 q = 1) (hb : d322043 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d318813, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318813, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d318966 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d318967 q = 1) (hb : d380504 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d318967, d380504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d318967, d380504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro108163 (p : Pattern) (ha : d380020 p = 1) (hb : d380510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380015 q = 1) (hb : d380505 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380015, d380505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108162 q ha hb
    | true =>
      simp only [d380015, d380505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380016 q = 1) (hb : d380506 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380016, d380506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380016, d380506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380017 q = 1) (hb : d380507 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380017, d380507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380017, d380507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380018 q = 1) (hb : d380508 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380018, d380508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380018, d380508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380019 q = 1) (hb : d380509 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380019, d380509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380019, d380509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380020 q = 1) (hb : d380510 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380020, d380510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380020, d380510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108164 (p : Pattern) (ha : d380026 p = 1) (hb : d380516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380021 q = 1) (hb : d380511 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380021, d380511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108163 q ha hb
    | true =>
      simp only [d380021, d380511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380022 q = 1) (hb : d380512 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380022, d380512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380022, d380512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380023 q = 1) (hb : d380513 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380023, d380513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380023, d380513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380024 q = 1) (hb : d380514 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380024, d380514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380024, d380514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380025 q = 1) (hb : d380515 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380025, d380515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380025, d380515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380026 q = 1) (hb : d380516 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380026, d380516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380026, d380516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108165 (p : Pattern) (ha : d380032 p = 1) (hb : d380522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380027 q = 1) (hb : d380517 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380027, d380517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108164 q ha hb
    | true =>
      simp only [d380027, d380517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380028 q = 1) (hb : d380518 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380028, d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380028, d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380029 q = 1) (hb : d380519 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380029, d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380029, d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380030 q = 1) (hb : d380520 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380030, d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380030, d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380031 q = 1) (hb : d380521 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380031, d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380031, d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380032 q = 1) (hb : d380522 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380032, d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380032, d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108166 (p : Pattern) (ha : d380038 p = 1) (hb : d380528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380033 q = 1) (hb : d380523 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380033, d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108165 q ha hb
    | true =>
      simp only [d380033, d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380034 q = 1) (hb : d380524 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380034, d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380034, d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380035 q = 1) (hb : d380525 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380035, d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380035, d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380036 q = 1) (hb : d380526 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380036, d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380036, d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380037 q = 1) (hb : d380527 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380037, d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380037, d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380038 q = 1) (hb : d380528 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380038, d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380038, d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108167 (p : Pattern) (ha : d380044 p = 1) (hb : d380534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380039 q = 1) (hb : d380529 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380039, d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108166 q ha hb
    | true =>
      simp only [d380039, d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380040 q = 1) (hb : d380530 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380040, d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380040, d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380041 q = 1) (hb : d380531 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380041, d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380041, d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380042 q = 1) (hb : d380532 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380042, d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380042, d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380043 q = 1) (hb : d380533 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380043, d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380043, d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380044 q = 1) (hb : d380534 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380044, d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380044, d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108168 (p : Pattern) (ha : d380050 p = 1) (hb : d380540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380045 q = 1) (hb : d380535 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380045, d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108167 q ha hb
    | true =>
      simp only [d380045, d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380046 q = 1) (hb : d380536 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380046, d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380046, d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380047 q = 1) (hb : d380537 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380047, d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380047, d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380048 q = 1) (hb : d380538 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380048, d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380048, d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380049 q = 1) (hb : d380539 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380049, d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380049, d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380050 q = 1) (hb : d380540 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380050, d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380050, d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108169 (p : Pattern) (ha : d380056 p = 1) (hb : d380546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380051 q = 1) (hb : d380541 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380051, d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108168 q ha hb
    | true =>
      simp only [d380051, d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380052 q = 1) (hb : d380542 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380052, d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380052, d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380053 q = 1) (hb : d380543 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380053, d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380053, d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380054 q = 1) (hb : d380544 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380054, d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380054, d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380055 q = 1) (hb : d380545 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380055, d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380055, d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380056 q = 1) (hb : d380546 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380056, d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380056, d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108170 (p : Pattern) (ha : d380062 p = 1) (hb : d380552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380057 q = 1) (hb : d380547 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380057, d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108169 q ha hb
    | true =>
      simp only [d380057, d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380058 q = 1) (hb : d380548 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380058, d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380058, d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380059 q = 1) (hb : d380549 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380059, d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380059, d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380060 q = 1) (hb : d380550 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380060, d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380060, d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380061 q = 1) (hb : d380551 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380061, d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380061, d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380062 q = 1) (hb : d380552 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380062, d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380062, d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108171 (p : Pattern) (ha : d380454 p = 1) (hb : d380601 p = 1) : d380601 p = 1 := by
  have h0 (q : Pattern) (ha : d380454 q = 1) (hb : d380601 q = 1) : d380601 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro108172 (p : Pattern) (ha : d318967 p = 1) (hb : d380553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d318809 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d318809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d318809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86335 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d318810 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d318810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d318810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d318811 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d318811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d318811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d318812 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d318812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d318812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d318813 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d318813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d318813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d318966 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d318967 q = 1) (hb : d380553 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d318967, d380553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d318967, d380553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro108173 (p : Pattern) (ha : d380020 p = 1) (hb : d380559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380015 q = 1) (hb : d380554 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380015, d380554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108172 q ha hb
    | true =>
      simp only [d380015, d380554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380016 q = 1) (hb : d380555 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380016, d380555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380016, d380555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380017 q = 1) (hb : d380556 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380017, d380556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380017, d380556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380018 q = 1) (hb : d380557 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380018, d380557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380018, d380557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380019 q = 1) (hb : d380558 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380019, d380558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380019, d380558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380020 q = 1) (hb : d380559 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380020, d380559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380020, d380559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108174 (p : Pattern) (ha : d380026 p = 1) (hb : d380565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380021 q = 1) (hb : d380560 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380021, d380560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108173 q ha hb
    | true =>
      simp only [d380021, d380560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380022 q = 1) (hb : d380561 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380022, d380561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380022, d380561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380023 q = 1) (hb : d380562 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380023, d380562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380023, d380562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380024 q = 1) (hb : d380563 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380024, d380563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380024, d380563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380025 q = 1) (hb : d380564 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380025, d380564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380025, d380564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380026 q = 1) (hb : d380565 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380026, d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380026, d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108175 (p : Pattern) (ha : d380032 p = 1) (hb : d380571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380027 q = 1) (hb : d380566 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380027, d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108174 q ha hb
    | true =>
      simp only [d380027, d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380028 q = 1) (hb : d380567 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380028, d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380028, d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380029 q = 1) (hb : d380568 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380029, d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380029, d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380030 q = 1) (hb : d380569 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380030, d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380030, d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380031 q = 1) (hb : d380570 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380031, d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380031, d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380032 q = 1) (hb : d380571 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380032, d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380032, d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108176 (p : Pattern) (ha : d380038 p = 1) (hb : d380577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380033 q = 1) (hb : d380572 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380033, d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108175 q ha hb
    | true =>
      simp only [d380033, d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380034 q = 1) (hb : d380573 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380034, d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380034, d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380035 q = 1) (hb : d380574 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380035, d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380035, d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380036 q = 1) (hb : d380575 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380036, d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380036, d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380037 q = 1) (hb : d380576 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380037, d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380037, d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380038 q = 1) (hb : d380577 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380038, d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380038, d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108177 (p : Pattern) (ha : d380044 p = 1) (hb : d380583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380039 q = 1) (hb : d380578 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380039, d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108176 q ha hb
    | true =>
      simp only [d380039, d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380040 q = 1) (hb : d380579 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380040, d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380040, d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380041 q = 1) (hb : d380580 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380041, d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380041, d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380042 q = 1) (hb : d380581 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380042, d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380042, d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380043 q = 1) (hb : d380582 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380043, d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380043, d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380044 q = 1) (hb : d380583 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380044, d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380044, d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108178 (p : Pattern) (ha : d380050 p = 1) (hb : d380589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380045 q = 1) (hb : d380584 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380045, d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108177 q ha hb
    | true =>
      simp only [d380045, d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380046 q = 1) (hb : d380585 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380046, d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380046, d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380047 q = 1) (hb : d380586 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380047, d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380047, d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380048 q = 1) (hb : d380587 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380048, d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380048, d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380049 q = 1) (hb : d380588 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380049, d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380049, d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380050 q = 1) (hb : d380589 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380050, d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380050, d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108179 (p : Pattern) (ha : d380056 p = 1) (hb : d380595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380051 q = 1) (hb : d380590 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380051, d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108178 q ha hb
    | true =>
      simp only [d380051, d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380052 q = 1) (hb : d380591 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380052, d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380052, d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380053 q = 1) (hb : d380592 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380053, d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380053, d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380054 q = 1) (hb : d380593 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380054, d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380054, d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380055 q = 1) (hb : d380594 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380055, d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380055, d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380056 q = 1) (hb : d380595 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380056, d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380056, d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108180 (p : Pattern) (ha : d380062 p = 1) (hb : d380601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380057 q = 1) (hb : d380596 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380057, d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108179 q ha hb
    | true =>
      simp only [d380057, d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380058 q = 1) (hb : d380597 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380058, d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380058, d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380059 q = 1) (hb : d380598 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380059, d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380059, d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380060 q = 1) (hb : d380599 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380060, d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380060, d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380061 q = 1) (hb : d380600 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380061, d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380061, d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380062 q = 1) (hb : d380601 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380062, d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380062, d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108181 (p : Pattern) (ha : d322082 p = 1) (hb : d380553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d322039 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86400 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d322040 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d322041 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d322042 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d322043 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d322081 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d322082 q = 1) (hb : d380553 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d322082, d380553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d322082, d380553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro108182 (p : Pattern) (ha : d380068 p = 1) (hb : d380559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380063 q = 1) (hb : d380554 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380063, d380554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108181 q ha hb
    | true =>
      simp only [d380063, d380554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380064 q = 1) (hb : d380555 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380064, d380555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380064, d380555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380065 q = 1) (hb : d380556 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380065, d380556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380065, d380556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380066 q = 1) (hb : d380557 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380066, d380557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380066, d380557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380067 q = 1) (hb : d380558 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380067, d380558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380067, d380558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380068 q = 1) (hb : d380559 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380068, d380559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380068, d380559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108183 (p : Pattern) (ha : d380074 p = 1) (hb : d380565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380069 q = 1) (hb : d380560 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380069, d380560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108182 q ha hb
    | true =>
      simp only [d380069, d380560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380070 q = 1) (hb : d380561 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380070, d380561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380070, d380561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380071 q = 1) (hb : d380562 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380071, d380562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380071, d380562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380072 q = 1) (hb : d380563 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380072, d380563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380072, d380563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380073 q = 1) (hb : d380564 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380073, d380564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380073, d380564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380074 q = 1) (hb : d380565 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380074, d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380074, d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108184 (p : Pattern) (ha : d380080 p = 1) (hb : d380571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380075 q = 1) (hb : d380566 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380075, d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108183 q ha hb
    | true =>
      simp only [d380075, d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380076 q = 1) (hb : d380567 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380076, d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380076, d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380077 q = 1) (hb : d380568 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380077, d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380077, d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380078 q = 1) (hb : d380569 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380078, d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380078, d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380079 q = 1) (hb : d380570 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380079, d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380079, d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380080 q = 1) (hb : d380571 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380080, d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380080, d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108185 (p : Pattern) (ha : d380086 p = 1) (hb : d380577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380081 q = 1) (hb : d380572 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380081, d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108184 q ha hb
    | true =>
      simp only [d380081, d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380082 q = 1) (hb : d380573 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380082, d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380082, d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380083 q = 1) (hb : d380574 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380083, d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380083, d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380084 q = 1) (hb : d380575 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380084, d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380084, d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380085 q = 1) (hb : d380576 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380085, d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380085, d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380086 q = 1) (hb : d380577 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380086, d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380086, d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108186 (p : Pattern) (ha : d380092 p = 1) (hb : d380583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380087 q = 1) (hb : d380578 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380087, d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108185 q ha hb
    | true =>
      simp only [d380087, d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380088 q = 1) (hb : d380579 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380088, d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380088, d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380089 q = 1) (hb : d380580 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380089, d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380089, d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380090 q = 1) (hb : d380581 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380090, d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380090, d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380091 q = 1) (hb : d380582 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380091, d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380091, d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380092 q = 1) (hb : d380583 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380092, d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380092, d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108187 (p : Pattern) (ha : d380098 p = 1) (hb : d380589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380093 q = 1) (hb : d380584 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380093, d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108186 q ha hb
    | true =>
      simp only [d380093, d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380094 q = 1) (hb : d380585 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380094, d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380094, d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380095 q = 1) (hb : d380586 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380095, d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380095, d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380096 q = 1) (hb : d380587 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380096, d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380096, d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380097 q = 1) (hb : d380588 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380097, d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380097, d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380098 q = 1) (hb : d380589 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380098, d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380098, d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108188 (p : Pattern) (ha : d380104 p = 1) (hb : d380595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380099 q = 1) (hb : d380590 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380099, d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108187 q ha hb
    | true =>
      simp only [d380099, d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380100 q = 1) (hb : d380591 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380100, d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380100, d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380101 q = 1) (hb : d380592 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380101, d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380101, d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380102 q = 1) (hb : d380593 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380102, d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380102, d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380103 q = 1) (hb : d380594 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380103, d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380103, d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380104 q = 1) (hb : d380595 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380104, d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380104, d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108189 (p : Pattern) (ha : d380110 p = 1) (hb : d380601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380105 q = 1) (hb : d380596 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380105, d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108188 q ha hb
    | true =>
      simp only [d380105, d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380106 q = 1) (hb : d380597 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380106, d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380106, d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380107 q = 1) (hb : d380598 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380107, d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380107, d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380108 q = 1) (hb : d380599 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380108, d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380108, d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380109 q = 1) (hb : d380600 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380109, d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380109, d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380110 q = 1) (hb : d380601 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380110, d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380110, d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108190 (p : Pattern) (ha : d380516 p = 1) (hb : d380924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380515 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380923 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380516 q = 1) (hb : d380924 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380516, d380924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d380516, d380924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro108191 (p : Pattern) (ha : d380522 p = 1) (hb : d380925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380517 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380517, d380925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108190 q ha hb
    | true =>
      simp only [d380517, d380925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d380518 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d380519 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d380520 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d380521 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d380522 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro108192 (p : Pattern) (ha : d380528 p = 1) (hb : d380925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380523 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108191 q ha hb
    | true =>
      simp only [d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380524 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380525 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380526 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380527 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380528 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108193 (p : Pattern) (ha : d380534 p = 1) (hb : d380925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380529 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108192 q ha hb
    | true =>
      simp only [d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380530 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380531 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380532 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380533 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380534 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108194 (p : Pattern) (ha : d380540 p = 1) (hb : d380925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380535 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108193 q ha hb
    | true =>
      simp only [d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380536 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380537 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380538 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380539 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380540 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108195 (p : Pattern) (ha : d380546 p = 1) (hb : d380925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380541 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108194 q ha hb
    | true =>
      simp only [d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380542 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380543 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380544 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380545 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380546 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108196 (p : Pattern) (ha : d380552 p = 1) (hb : d380925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380547 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108195 q ha hb
    | true =>
      simp only [d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380548 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380549 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380550 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380551 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380552 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108197 (p : Pattern) (ha : d0 p = 1) (hb : d381015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381015 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108198 (p : Pattern) (ha : d380565 p = 1) (hb : d380924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380564 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380923 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380565 q = 1) (hb : d380924 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380565, d380924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d380565, d380924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro108199 (p : Pattern) (ha : d380571 p = 1) (hb : d380925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380566 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380566, d380925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108198 q ha hb
    | true =>
      simp only [d380566, d380925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d380567 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d380568 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d380569 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d380570 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d380571 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro108200 (p : Pattern) (ha : d380577 p = 1) (hb : d380925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380572 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108199 q ha hb
    | true =>
      simp only [d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380573 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380574 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380575 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380576 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380577 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108201 (p : Pattern) (ha : d380583 p = 1) (hb : d380925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380578 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108200 q ha hb
    | true =>
      simp only [d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380579 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380580 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380581 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380582 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380583 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108202 (p : Pattern) (ha : d380589 p = 1) (hb : d380925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380584 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108201 q ha hb
    | true =>
      simp only [d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380585 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380586 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380587 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380588 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380589 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108203 (p : Pattern) (ha : d380595 p = 1) (hb : d380925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380590 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108202 q ha hb
    | true =>
      simp only [d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380591 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380592 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380593 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380594 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380595 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108204 (p : Pattern) (ha : d380601 p = 1) (hb : d380925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380596 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108203 q ha hb
    | true =>
      simp only [d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380597 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380598 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380599 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380600 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380601 q = 1) (hb : d380925 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108205 (p : Pattern) (ha : d0 p = 1) (hb : d381060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381060 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108206 (p : Pattern) (ha : d380311 p = 1) (hb : d380516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380515 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380310 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380311 q = 1) (hb : d380516 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380311, d380516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380311, d380516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro108207 (p : Pattern) (ha : d380312 p = 1) (hb : d380522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380312 q = 1) (hb : d380517 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380312, d380517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108206 q ha hb
    | true =>
      simp only [d380312, d380517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d380312 q = 1) (hb : d380518 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d380312 q = 1) (hb : d380519 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d380312 q = 1) (hb : d380520 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d380312 q = 1) (hb : d380521 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d380312 q = 1) (hb : d380522 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h7 p ha hb
theorem andIntro108208 (p : Pattern) (ha : d380312 p = 1) (hb : d380528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380312 q = 1) (hb : d380523 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108207 q ha hb
    | true =>
      simp only [d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380312 q = 1) (hb : d380524 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380312 q = 1) (hb : d380525 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380312 q = 1) (hb : d380526 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380312 q = 1) (hb : d380527 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380312 q = 1) (hb : d380528 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108209 (p : Pattern) (ha : d380312 p = 1) (hb : d380534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380312 q = 1) (hb : d380529 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108208 q ha hb
    | true =>
      simp only [d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380312 q = 1) (hb : d380530 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380312 q = 1) (hb : d380531 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380312 q = 1) (hb : d380532 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380312 q = 1) (hb : d380533 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380312 q = 1) (hb : d380534 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108210 (p : Pattern) (ha : d380312 p = 1) (hb : d380540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380312 q = 1) (hb : d380535 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108209 q ha hb
    | true =>
      simp only [d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380312 q = 1) (hb : d380536 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380312 q = 1) (hb : d380537 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380312 q = 1) (hb : d380538 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380312 q = 1) (hb : d380539 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380312 q = 1) (hb : d380540 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108211 (p : Pattern) (ha : d380312 p = 1) (hb : d380546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380312 q = 1) (hb : d380541 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108210 q ha hb
    | true =>
      simp only [d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380312 q = 1) (hb : d380542 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380312 q = 1) (hb : d380543 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380312 q = 1) (hb : d380544 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380312 q = 1) (hb : d380545 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380312 q = 1) (hb : d380546 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108212 (p : Pattern) (ha : d380312 p = 1) (hb : d380552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380312 q = 1) (hb : d380547 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108211 q ha hb
    | true =>
      simp only [d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380312 q = 1) (hb : d380548 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380312 q = 1) (hb : d380549 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380312 q = 1) (hb : d380550 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380312 q = 1) (hb : d380551 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380312 q = 1) (hb : d380552 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108213 (p : Pattern) (ha : d380311 p = 1) (hb : d380565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380564 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380310 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d380311 q = 1) (hb : d380565 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380311, d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380311, d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro108214 (p : Pattern) (ha : d380312 p = 1) (hb : d380571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380312 q = 1) (hb : d380566 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380312, d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108213 q ha hb
    | true =>
      simp only [d380312, d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d380312 q = 1) (hb : d380567 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d380312 q = 1) (hb : d380568 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d380312 q = 1) (hb : d380569 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d380312 q = 1) (hb : d380570 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d380312 q = 1) (hb : d380571 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h7 p ha hb
theorem andIntro108215 (p : Pattern) (ha : d380312 p = 1) (hb : d380577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380312 q = 1) (hb : d380572 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108214 q ha hb
    | true =>
      simp only [d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380312 q = 1) (hb : d380573 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380312 q = 1) (hb : d380574 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380312 q = 1) (hb : d380575 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380312 q = 1) (hb : d380576 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380312 q = 1) (hb : d380577 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108216 (p : Pattern) (ha : d380312 p = 1) (hb : d380583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380312 q = 1) (hb : d380578 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108215 q ha hb
    | true =>
      simp only [d380578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380312 q = 1) (hb : d380579 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380312 q = 1) (hb : d380580 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380312 q = 1) (hb : d380581 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380312 q = 1) (hb : d380582 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380312 q = 1) (hb : d380583 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108217 (p : Pattern) (ha : d380312 p = 1) (hb : d380589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380312 q = 1) (hb : d380584 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108216 q ha hb
    | true =>
      simp only [d380584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380312 q = 1) (hb : d380585 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380312 q = 1) (hb : d380586 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380312 q = 1) (hb : d380587 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380312 q = 1) (hb : d380588 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380312 q = 1) (hb : d380589 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108218 (p : Pattern) (ha : d380312 p = 1) (hb : d380595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380312 q = 1) (hb : d380590 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108217 q ha hb
    | true =>
      simp only [d380590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380312 q = 1) (hb : d380591 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380312 q = 1) (hb : d380592 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380312 q = 1) (hb : d380593 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380312 q = 1) (hb : d380594 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380312 q = 1) (hb : d380595 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108219 (p : Pattern) (ha : d380312 p = 1) (hb : d380601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380312 q = 1) (hb : d380596 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108218 q ha hb
    | true =>
      simp only [d380596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380312 q = 1) (hb : d380597 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380312 q = 1) (hb : d380598 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380312 q = 1) (hb : d380599 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380312 q = 1) (hb : d380600 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380312 q = 1) (hb : d380601 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro108220 (p : Pattern) (ha : d47563 p = 1) (hb : d381064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d98 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d99 q = 1) (hb : d366035 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d366035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d366035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d47562 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d47562, d381064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47562, d381064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d47563 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d47563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro108221 (p : Pattern) (ha : d47569 p = 1) (hb : d381064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47564 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108220 q ha hb
    | true =>
      simp only [d47564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47565 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47566 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47567 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47568 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47569 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108222 (p : Pattern) (ha : d47575 p = 1) (hb : d381066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47570 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108221 q ha hb
    | true =>
      simp only [d47570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47571 q = 1) (hb : d381064 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d47572 q = 1) (hb : d381065 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47572, d381065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47572, d381065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47573 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47573, d381066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47573, d381066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d47574 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47575 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro108223 (p : Pattern) (ha : d47581 p = 1) (hb : d381066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47576 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108222 q ha hb
    | true =>
      simp only [d47576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47577 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47578 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47579 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47580 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47581 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108224 (p : Pattern) (ha : d47587 p = 1) (hb : d381066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47582 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108223 q ha hb
    | true =>
      simp only [d47582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47583 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47584 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47585 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47586 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47587 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108225 (p : Pattern) (ha : d47593 p = 1) (hb : d381066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47588 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108224 q ha hb
    | true =>
      simp only [d47588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47589 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47590 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47591 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47592 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47593 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108226 (p : Pattern) (ha : d47599 p = 1) (hb : d381066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47594 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108225 q ha hb
    | true =>
      simp only [d47594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47595 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47596 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47597 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47598 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47599 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108227 (p : Pattern) (ha : d47605 p = 1) (hb : d381066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47600 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108226 q ha hb
    | true =>
      simp only [d47600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47601 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47602 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47603 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47604 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47605 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108228 (p : Pattern) (ha : d47611 p = 1) (hb : d381066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47606 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108227 q ha hb
    | true =>
      simp only [d47606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47607 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47608 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47609 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47610 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47611 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108229 (p : Pattern) (ha : d0 p = 1) (hb : d381066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381066 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108230 (p : Pattern) (ha : d47575 p = 1) (hb : d381075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d47571 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d381073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d47572 q = 1) (hb : d381074 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47572, d381074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47572, d381074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d47573 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47573, d381075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47573, d381075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d47574 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47575 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro108231 (p : Pattern) (ha : d47581 p = 1) (hb : d381075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47576 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108230 q ha hb
    | true =>
      simp only [d47576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47577 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47578 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47579 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47580 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47581 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108232 (p : Pattern) (ha : d47587 p = 1) (hb : d381075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47582 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108231 q ha hb
    | true =>
      simp only [d47582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47583 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47584 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47585 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47586 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47587 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108233 (p : Pattern) (ha : d47593 p = 1) (hb : d381075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47588 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108232 q ha hb
    | true =>
      simp only [d47588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47589 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47590 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47591 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47592 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47593 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108234 (p : Pattern) (ha : d47599 p = 1) (hb : d381075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47594 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108233 q ha hb
    | true =>
      simp only [d47594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47595 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47596 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47597 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47598 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47599 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108235 (p : Pattern) (ha : d47605 p = 1) (hb : d381075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47600 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108234 q ha hb
    | true =>
      simp only [d47600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47601 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47602 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47603 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47604 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47605 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108236 (p : Pattern) (ha : d47611 p = 1) (hb : d381075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47606 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108235 q ha hb
    | true =>
      simp only [d47606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47607 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47608 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47609 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47610 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47611 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108237 (p : Pattern) (ha : d0 p = 1) (hb : d381075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381075 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108238 (p : Pattern) (ha : d47575 p = 1) (hb : d381079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d47571 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d381077 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d47572 q = 1) (hb : d381078 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47572, d381078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47572, d381078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d47573 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47573, d381079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47573, d381079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d47574 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47575 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro108239 (p : Pattern) (ha : d47581 p = 1) (hb : d381079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47576 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108238 q ha hb
    | true =>
      simp only [d47576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47577 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47578 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47579 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47580 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47581 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108240 (p : Pattern) (ha : d47587 p = 1) (hb : d381079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47582 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108239 q ha hb
    | true =>
      simp only [d47582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47583 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47584 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47585 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47586 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47587 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108241 (p : Pattern) (ha : d47593 p = 1) (hb : d381079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47588 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108240 q ha hb
    | true =>
      simp only [d47588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47589 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47590 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47591 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47592 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47593 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108242 (p : Pattern) (ha : d47599 p = 1) (hb : d381079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47594 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108241 q ha hb
    | true =>
      simp only [d47594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47595 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47596 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47597 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47598 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47599 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108243 (p : Pattern) (ha : d47605 p = 1) (hb : d381079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47600 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108242 q ha hb
    | true =>
      simp only [d47600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47601 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47602 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47603 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47604 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47605 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108244 (p : Pattern) (ha : d47611 p = 1) (hb : d381079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47606 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108243 q ha hb
    | true =>
      simp only [d47606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47607 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47608 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47609 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47610 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47611 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108245 (p : Pattern) (ha : d0 p = 1) (hb : d381079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381079 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108246 (p : Pattern) (ha : d47611 p = 1) (hb : d380855 p = 1) : d47611 p = 1 := by
  have h0 (q : Pattern) (ha : d47611 q = 1) (hb : d380855 q = 1) : d47611 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108247 (p : Pattern) (ha : d47563 p = 1) (hb : d380455 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d318812 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d47562 q = 1) (hb : d318813 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d47562, d318813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47562, d318813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47563 q = 1) (hb : d380455 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d47563, d380455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47563, d380455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro108248 (p : Pattern) (ha : d47569 p = 1) (hb : d380461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47564 q = 1) (hb : d380456 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47564, d380456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108247 q ha hb
    | true =>
      simp only [d47564, d380456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47565 q = 1) (hb : d380457 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47565, d380457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47565, d380457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47566 q = 1) (hb : d380458 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47566, d380458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47566, d380458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47567 q = 1) (hb : d380459 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47567, d380459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47567, d380459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47568 q = 1) (hb : d380460 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47568, d380460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47568, d380460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47569 q = 1) (hb : d380461 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47569, d380461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47569, d380461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108249 (p : Pattern) (ha : d47575 p = 1) (hb : d380467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47570 q = 1) (hb : d380462 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47570, d380462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108248 q ha hb
    | true =>
      simp only [d47570, d380462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47571 q = 1) (hb : d380463 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47571, d380463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47571, d380463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47572 q = 1) (hb : d380464 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47572, d380464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47572, d380464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47573 q = 1) (hb : d380465 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47573, d380465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47573, d380465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47574 q = 1) (hb : d380466 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47574, d380466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47574, d380466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47575 q = 1) (hb : d380467 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47575, d380467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47575, d380467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
