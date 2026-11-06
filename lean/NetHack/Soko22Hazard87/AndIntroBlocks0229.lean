import NetHack.Soko22Hazard87.AndIntroBlocks0228
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro57250 (p : Pattern) (ha : d234225 p = 1) (hb : d235637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234120 q = 1) (hb : d235541 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234120, d235541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57228 q ha hb
    | true =>
      simp only [d234120, d235541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234121 q = 1) (hb : d235542 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234121, d235542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234121, d235542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234124 q = 1) (hb : d235545 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234124, d235545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57229 q ha hb
    | true =>
      simp only [d234124, d235545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234125 q = 1) (hb : d235546 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234125, d235546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234125, d235546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234126 q = 1) (hb : d235547 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234126, d235547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234126, d235547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234161 q = 1) (hb : d235582 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234161, d235582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234161, d235582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234162 q = 1) (hb : d235583 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234162, d235583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234162, d235583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234225 q = 1) (hb : d235637 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234225, d235637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234225, d235637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro57251 (p : Pattern) (ha : d234226 p = 1) (hb : d235638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234124 q = 1) (hb : d235545 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234124, d235545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57229 q ha hb
    | true =>
      simp only [d234124, d235545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234125 q = 1) (hb : d235546 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234125, d235546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234125, d235546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234130 q = 1) (hb : d235551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234130, d235551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234130, d235551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234164 q = 1) (hb : d235585 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234164, d235585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234164, d235585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234165 q = 1) (hb : d235586 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234165, d235586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234165, d235586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234226 q = 1) (hb : d235638 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234226, d235638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234226, d235638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57252 (p : Pattern) (ha : d234230 p = 1) (hb : d235642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234184 q = 1) (hb : d235604 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234184, d235604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57242 q ha hb
    | true =>
      simp only [d234184, d235604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234185 q = 1) (hb : d235605 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234185, d235605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234185, d235605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234120 q = 1) (hb : d235541 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234120, d235541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57228 q ha hb
    | true =>
      simp only [d234120, d235541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234121 q = 1) (hb : d235542 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234121, d235542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234121, d235542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234186 q = 1) (hb : d235606 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234186, d235606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234186, d235606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234187 q = 1) (hb : d235607 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234187, d235607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234187, d235607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234188 q = 1) (hb : d235608 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234188, d235608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234188, d235608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234230 q = 1) (hb : d235642 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234230, d235642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234230, d235642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro57253 (p : Pattern) (ha : d234233 p = 1) (hb : d235645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234207 q = 1) (hb : d235619 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234207, d235619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57245 q ha hb
    | true =>
      simp only [d234207, d235619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234208 q = 1) (hb : d235620 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234208, d235620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234208, d235620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234209 q = 1) (hb : d235621 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234209, d235621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234209, d235621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234210 q = 1) (hb : d235622 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234210, d235622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234210, d235622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234211 q = 1) (hb : d235623 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234211, d235623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234211, d235623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234233 q = 1) (hb : d235645 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234233, d235645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234233, d235645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57254 (p : Pattern) (ha : d234239 p = 1) (hb : d235651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234157 q = 1) (hb : d235578 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234157, d235578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57236 q ha hb
    | true =>
      simp only [d234157, d235578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57237 q ha hb
  have h2 (q : Pattern) (ha : d234158 q = 1) (hb : d235579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234158, d235579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234158, d235579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234159 q = 1) (hb : d235580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234159, d235580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234159, d235580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234160 q = 1) (hb : d235581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234160, d235581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234160, d235581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234167 q = 1) (hb : d235588 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234167, d235588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57238 q ha hb
    | true =>
      simp only [d234167, d235588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57239 q ha hb
  have h6 (q : Pattern) (ha : d234168 q = 1) (hb : d235589 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234168, d235589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234168, d235589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234169 q = 1) (hb : d235590 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234169, d235590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234169, d235590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234190 q = 1) (hb : d235610 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234190, d235610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57243 q ha hb
    | true =>
      simp only [d234190, d235610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57230 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d234134 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d234191 q = 1) (hb : d235611 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234191, d235611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234191, d235611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d234213 q = 1) (hb : d235625 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234213, d235625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57246 q ha hb
    | true =>
      simp only [d234213, d235625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d234214 q = 1) (hb : d235626 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234214, d235626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234214, d235626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d234215 q = 1) (hb : d235627 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234215, d235627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d234215, d235627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234216 q = 1) (hb : d235628 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234216, d235628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234216, d235628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d234217 q = 1) (hb : d235629 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234217, d235629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234217, d235629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d234221 q = 1) (hb : d235633 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234221, d235633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57248 q ha hb
    | true =>
      simp only [d234221, d235633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57249 q ha hb
  have h17 (q : Pattern) (ha : d234222 q = 1) (hb : d235634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234222, d235634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234222, d235634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d234223 q = 1) (hb : d235635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234223, d235635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d234223, d235635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d234224 q = 1) (hb : d235636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234224, d235636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234224, d235636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d234227 q = 1) (hb : d235639 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234227, d235639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57250 q ha hb
    | true =>
      simp only [d234227, d235639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57251 q ha hb
  have h21 (q : Pattern) (ha : d234228 q = 1) (hb : d235640 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234228, d235640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234228, d235640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d234229 q = 1) (hb : d235641 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234229, d235641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d234229, d235641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d234231 q = 1) (hb : d235643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234231, d235643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57252 q ha hb
    | true =>
      simp only [d234231, d235643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57233 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d234144 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d234232 q = 1) (hb : d235644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234232, d235644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d234232, d235644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d234234 q = 1) (hb : d235646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234234, d235646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57253 q ha hb
    | true =>
      simp only [d234234, d235646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d234235 q = 1) (hb : d235647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234235, d235647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d234235, d235647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d234236 q = 1) (hb : d235648 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234236, d235648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d234236, d235648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d234237 q = 1) (hb : d235649 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234237, d235649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d234237, d235649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d234238 q = 1) (hb : d235650 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234238, d235650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d234238, d235650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d234239 q = 1) (hb : d235651 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234239, d235651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d234239, d235651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro57255 (p : Pattern) (ha : d234246 p = 1) (hb : d235658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234134 q = 1) (hb : d235555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234134, d235555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57230 q ha hb
    | true =>
      simp only [d234134, d235555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57231 q ha hb
  have h2 (q : Pattern) (ha : d234135 q = 1) (hb : d235556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234135, d235556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234135, d235556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234136 q = 1) (hb : d235557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234136, d235557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234136, d235557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234137 q = 1) (hb : d235558 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234137, d235558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234137, d235558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234138 q = 1) (hb : d235559 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234138, d235559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234138, d235559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234241 q = 1) (hb : d235653 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234241, d235653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57231 q ha hb
    | true =>
      simp only [d234241, d235653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234242 q = 1) (hb : d235654 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234242, d235654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234242, d235654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234243 q = 1) (hb : d235655 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234243, d235655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234243, d235655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234244 q = 1) (hb : d235656 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234244, d235656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234244, d235656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234245 q = 1) (hb : d235657 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234245, d235657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234245, d235657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234246 q = 1) (hb : d235658 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234246, d235658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234246, d235658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro57256 (p : Pattern) (ha : d234252 p = 1) (hb : d235664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234241 q = 1) (hb : d235653 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234241, d235653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57231 q ha hb
    | true =>
      simp only [d234241, d235653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234242 q = 1) (hb : d235654 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234242, d235654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234242, d235654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234243 q = 1) (hb : d235655 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234243, d235655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234243, d235655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234244 q = 1) (hb : d235656 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234244, d235656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234244, d235656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234245 q = 1) (hb : d235657 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234245, d235657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234245, d235657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234247 q = 1) (hb : d235659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234247, d235659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57234 q ha hb
    | true =>
      simp only [d234247, d235659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234248 q = 1) (hb : d235660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234248, d235660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234248, d235660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234249 q = 1) (hb : d235661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234249, d235661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234249, d235661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234250 q = 1) (hb : d235662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234250, d235662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234250, d235662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234251 q = 1) (hb : d235663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234251, d235663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234251, d235663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234252 q = 1) (hb : d235664 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234252, d235664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234252, d235664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro57257 (p : Pattern) (ha : d234259 p = 1) (hb : d235671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234231 q = 1) (hb : d235643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234231, d235643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57252 q ha hb
    | true =>
      simp only [d234231, d235643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57233 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234232 q = 1) (hb : d235644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234232, d235644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234232, d235644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d234234 q = 1) (hb : d235646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234234, d235646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57253 q ha hb
    | true =>
      simp only [d234234, d235646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234235 q = 1) (hb : d235647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234235, d235647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234235, d235647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234236 q = 1) (hb : d235648 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234236, d235648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234236, d235648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234257 q = 1) (hb : d235669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234257, d235669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234257, d235669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234258 q = 1) (hb : d235670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234258, d235670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234258, d235670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234259 q = 1) (hb : d235671 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234259, d235671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234259, d235671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro57258 (p : Pattern) (ha : d234261 p = 1) (hb : d235673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234247 q = 1) (hb : d235659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234247, d235659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57234 q ha hb
    | true =>
      simp only [d234247, d235659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234248 q = 1) (hb : d235660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234248, d235660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234248, d235660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234249 q = 1) (hb : d235661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234249, d235661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234249, d235661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234250 q = 1) (hb : d235662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234250, d235662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234250, d235662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234251 q = 1) (hb : d235663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234251, d235663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234251, d235663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234261 q = 1) (hb : d235673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234261, d235673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234261, d235673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57259 (p : Pattern) (ha : d234281 p = 1) (hb : d235693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234267 q = 1) (hb : d235679 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234267, d235679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234267, d235679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57240 q ha hb
  have h2 (q : Pattern) (ha : d234172 q = 1) (hb : d235592 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234172, d235592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57240 q ha hb
    | true =>
      simp only [d234172, d235592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234268 q = 1) (hb : d235680 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234268, d235680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234268, d235680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234173 q = 1) (hb : d235593 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234173, d235593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234173, d235593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234269 q = 1) (hb : d235681 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234269, d235681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234269, d235681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234270 q = 1) (hb : d235682 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234270, d235682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234270, d235682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234271 q = 1) (hb : d235683 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234271, d235683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234271, d235683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57222 q ha hb
  have h8 (q : Pattern) (ha : d234088 q = 1) (hb : d235507 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234088, d235507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57222 q ha hb
    | true =>
      simp only [d234088, d235507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234272 q = 1) (hb : d235684 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234272, d235684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234272, d235684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234089 q = 1) (hb : d235508 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234089, d235508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234089, d235508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d234273 q = 1) (hb : d235685 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234273, d235685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234273, d235685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234274 q = 1) (hb : d235686 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234274, d235686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234274, d235686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d234275 q = 1) (hb : d235687 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234275, d235687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234275, d235687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234276 q = 1) (hb : d235688 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234276, d235688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234276, d235688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57223 q ha hb
  have h15 (q : Pattern) (ha : d234094 q = 1) (hb : d235514 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234094, d235514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57223 q ha hb
    | true =>
      simp only [d234094, d235514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d234277 q = 1) (hb : d235689 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234277, d235689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d234277, d235689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d234095 q = 1) (hb : d235515 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234095, d235515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d234095, d235515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d234278 q = 1) (hb : d235690 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234278, d235690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d234278, d235690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d234279 q = 1) (hb : d235691 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234279, d235691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d234279, d235691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d234280 q = 1) (hb : d235692 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234280, d235692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d234280, d235692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d234281 q = 1) (hb : d235693 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234281, d235693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234281, d235693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro57260 (p : Pattern) (ha : d234287 p = 1) (hb : d235699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234271 q = 1) (hb : d235683 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234271, d235683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234271, d235683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57222 q ha hb
  have h2 (q : Pattern) (ha : d234088 q = 1) (hb : d235507 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234088, d235507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57222 q ha hb
    | true =>
      simp only [d234088, d235507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234272 q = 1) (hb : d235684 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234272, d235684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234272, d235684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234089 q = 1) (hb : d235508 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234089, d235508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234089, d235508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234273 q = 1) (hb : d235685 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234273, d235685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234273, d235685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234274 q = 1) (hb : d235686 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234274, d235686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234274, d235686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234276 q = 1) (hb : d235688 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234276, d235688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234276, d235688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57223 q ha hb
  have h8 (q : Pattern) (ha : d234094 q = 1) (hb : d235514 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234094, d235514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57223 q ha hb
    | true =>
      simp only [d234094, d235514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234277 q = 1) (hb : d235689 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234277, d235689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234277, d235689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234095 q = 1) (hb : d235515 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234095, d235515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234095, d235515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d234278 q = 1) (hb : d235690 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234278, d235690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234278, d235690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234279 q = 1) (hb : d235691 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234279, d235691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234279, d235691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d234280 q = 1) (hb : d235692 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234280, d235692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234280, d235692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234282 q = 1) (hb : d235694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234282, d235694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234282, d235694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57224 q ha hb
  have h15 (q : Pattern) (ha : d234101 q = 1) (hb : d235522 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234101, d235522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57224 q ha hb
    | true =>
      simp only [d234101, d235522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d234283 q = 1) (hb : d235695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234283, d235695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d234283, d235695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d234102 q = 1) (hb : d235523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234102, d235523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d234102, d235523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d234284 q = 1) (hb : d235696 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234284, d235696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d234284, d235696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d234285 q = 1) (hb : d235697 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234285, d235697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d234285, d235697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d234286 q = 1) (hb : d235698 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234286, d235698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d234286, d235698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d234287 q = 1) (hb : d235699 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234287, d235699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234287, d235699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro57261 (p : Pattern) (ha : d234292 p = 1) (hb : d235704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234276 q = 1) (hb : d235688 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234276, d235688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234276, d235688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57223 q ha hb
  have h2 (q : Pattern) (ha : d234094 q = 1) (hb : d235514 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234094, d235514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57223 q ha hb
    | true =>
      simp only [d234094, d235514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234277 q = 1) (hb : d235689 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234277, d235689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234277, d235689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234095 q = 1) (hb : d235515 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234095, d235515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234095, d235515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234278 q = 1) (hb : d235690 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234278, d235690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234278, d235690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234279 q = 1) (hb : d235691 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234279, d235691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234279, d235691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234282 q = 1) (hb : d235694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234282, d235694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234282, d235694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57224 q ha hb
  have h8 (q : Pattern) (ha : d234101 q = 1) (hb : d235522 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234101, d235522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57224 q ha hb
    | true =>
      simp only [d234101, d235522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234283 q = 1) (hb : d235695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234283, d235695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234283, d235695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234102 q = 1) (hb : d235523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234102, d235523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234102, d235523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d234284 q = 1) (hb : d235696 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234284, d235696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234284, d235696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234285 q = 1) (hb : d235697 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234285, d235697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234285, d235697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d234286 q = 1) (hb : d235698 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234286, d235698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234286, d235698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234291 q = 1) (hb : d235703 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234291, d235703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d234291, d235703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d234292 q = 1) (hb : d235704 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234292, d235704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234292, d235704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro57262 (p : Pattern) (ha : d234297 p = 1) (hb : d235709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234282 q = 1) (hb : d235694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234282, d235694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234282, d235694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57224 q ha hb
  have h2 (q : Pattern) (ha : d234101 q = 1) (hb : d235522 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234101, d235522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57224 q ha hb
    | true =>
      simp only [d234101, d235522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234283 q = 1) (hb : d235695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234283, d235695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234283, d235695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234102 q = 1) (hb : d235523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234102, d235523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234102, d235523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234284 q = 1) (hb : d235696 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234284, d235696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234284, d235696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234285 q = 1) (hb : d235697 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234285, d235697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234285, d235697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234291 q = 1) (hb : d235703 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234291, d235703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234291, d235703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234297 q = 1) (hb : d235709 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234297, d235709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234297, d235709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro57263 (p : Pattern) (ha : d234303 p = 1) (hb : d235715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234288 q = 1) (hb : d235700 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234288, d235700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57259 q ha hb
    | true =>
      simp only [d234288, d235700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57260 q ha hb
  have h2 (q : Pattern) (ha : d234289 q = 1) (hb : d235701 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234289, d235701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234289, d235701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234290 q = 1) (hb : d235702 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234290, d235702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234290, d235702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234293 q = 1) (hb : d235705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234293, d235705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57260 q ha hb
    | true =>
      simp only [d234293, d235705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57261 q ha hb
  have h5 (q : Pattern) (ha : d234294 q = 1) (hb : d235706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234294, d235706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234294, d235706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234295 q = 1) (hb : d235707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234295, d235707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234295, d235707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234296 q = 1) (hb : d235708 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234296, d235708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234296, d235708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234298 q = 1) (hb : d235710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234298, d235710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57261 q ha hb
    | true =>
      simp only [d234298, d235710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57262 q ha hb
  have h9 (q : Pattern) (ha : d234299 q = 1) (hb : d235711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234299, d235711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234299, d235711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234300 q = 1) (hb : d235712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234300, d235712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234300, d235712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234301 q = 1) (hb : d235713 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234301, d235713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234301, d235713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234302 q = 1) (hb : d235714 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d234302, d235714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234302, d235714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234303 q = 1) (hb : d235715 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d234303, d235715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d234303, d235715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro57264 (p : Pattern) (ha : d234308 p = 1) (hb : d235720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234293 q = 1) (hb : d235705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234293, d235705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57260 q ha hb
    | true =>
      simp only [d234293, d235705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57261 q ha hb
  have h2 (q : Pattern) (ha : d234294 q = 1) (hb : d235706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234294, d235706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234294, d235706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234295 q = 1) (hb : d235707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234295, d235707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234295, d235707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234298 q = 1) (hb : d235710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234298, d235710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57261 q ha hb
    | true =>
      simp only [d234298, d235710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57262 q ha hb
  have h5 (q : Pattern) (ha : d234299 q = 1) (hb : d235711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234299, d235711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234299, d235711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234300 q = 1) (hb : d235712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234300, d235712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234300, d235712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234301 q = 1) (hb : d235713 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234301, d235713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234301, d235713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234306 q = 1) (hb : d235718 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234306, d235718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234306, d235718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234307 q = 1) (hb : d235719 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d234307, d235719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234307, d235719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234308 q = 1) (hb : d235720 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d234308, d235720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234308, d235720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro57265 (p : Pattern) (ha : d234314 p = 1) (hb : d235726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234304 q = 1) (hb : d235716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234304, d235716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57263 q ha hb
    | true =>
      simp only [d234304, d235716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234305 q = 1) (hb : d235717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234305, d235717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234305, d235717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234309 q = 1) (hb : d235721 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234309, d235721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57264 q ha hb
    | true =>
      simp only [d234309, d235721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234310 q = 1) (hb : d235722 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234310, d235722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234310, d235722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234311 q = 1) (hb : d235723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234311, d235723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234311, d235723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234312 q = 1) (hb : d235724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234312, d235724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234312, d235724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234313 q = 1) (hb : d235725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234313, d235725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234313, d235725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234314 q = 1) (hb : d235726 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234314, d235726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234314, d235726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro57266 (p : Pattern) (ha : d234316 p = 1) (hb : d235728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234298 q = 1) (hb : d235710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234298, d235710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57261 q ha hb
    | true =>
      simp only [d234298, d235710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57262 q ha hb
  have h2 (q : Pattern) (ha : d234299 q = 1) (hb : d235711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234299, d235711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234299, d235711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234300 q = 1) (hb : d235712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234300, d235712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234300, d235712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234306 q = 1) (hb : d235718 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234306, d235718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234306, d235718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234315 q = 1) (hb : d235727 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d234315, d235727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234315, d235727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234316 q = 1) (hb : d235728 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d234316, d235728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234316, d235728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57267 (p : Pattern) (ha : d234322 p = 1) (hb : d235734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234309 q = 1) (hb : d235721 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234309, d235721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57264 q ha hb
    | true =>
      simp only [d234309, d235721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234310 q = 1) (hb : d235722 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234310, d235722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234310, d235722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234317 q = 1) (hb : d235729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234317, d235729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57266 q ha hb
    | true =>
      simp only [d234317, d235729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234318 q = 1) (hb : d235730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234318, d235730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234318, d235730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234319 q = 1) (hb : d235731 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234319, d235731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234319, d235731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234320 q = 1) (hb : d235732 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234320, d235732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234320, d235732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234321 q = 1) (hb : d235733 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234321, d235733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234321, d235733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234322 q = 1) (hb : d235734 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234322, d235734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234322, d235734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro57268 (p : Pattern) (ha : d234335 p = 1) (hb : d235737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234276 q = 1) (hb : d235688 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234276, d235688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234276, d235688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57223 q ha hb
  have h2 (q : Pattern) (ha : d234094 q = 1) (hb : d235514 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234094, d235514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57223 q ha hb
    | true =>
      simp only [d234094, d235514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234277 q = 1) (hb : d235689 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234277, d235689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234277, d235689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234095 q = 1) (hb : d235515 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234095, d235515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234095, d235515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234278 q = 1) (hb : d235690 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234278, d235690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234278, d235690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234279 q = 1) (hb : d235691 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234279, d235691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234279, d235691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234282 q = 1) (hb : d235694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234282, d235694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234282, d235694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57224 q ha hb
  have h8 (q : Pattern) (ha : d234101 q = 1) (hb : d235522 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234101, d235522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57224 q ha hb
    | true =>
      simp only [d234101, d235522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234283 q = 1) (hb : d235695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234283, d235695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234283, d235695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234102 q = 1) (hb : d235523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234102, d235523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234102, d235523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d234284 q = 1) (hb : d235696 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234284, d235696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234284, d235696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234285 q = 1) (hb : d235697 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234285, d235697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234285, d235697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d234286 q = 1) (hb : d235698 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234286, d235698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234286, d235698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d234334 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d234335 q = 1) (hb : d235737 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234335, d235737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234335, d235737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro57269 (p : Pattern) (ha : d234342 p = 1) (hb : d235743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234293 q = 1) (hb : d235705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234293, d235705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57260 q ha hb
    | true =>
      simp only [d234293, d235705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57261 q ha hb
  have h2 (q : Pattern) (ha : d234294 q = 1) (hb : d235706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234294, d235706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234294, d235706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234295 q = 1) (hb : d235707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234295, d235707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234295, d235707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234298 q = 1) (hb : d235710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234298, d235710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57261 q ha hb
    | true =>
      simp only [d234298, d235710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57262 q ha hb
  have h5 (q : Pattern) (ha : d234299 q = 1) (hb : d235711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234299, d235711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234299, d235711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234300 q = 1) (hb : d235712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234300, d235712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234300, d235712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234301 q = 1) (hb : d235713 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234301, d235713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234301, d235713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d234336 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d234337 q = 1) (hb : d235738 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234337, d235738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57268 q ha hb
    | true =>
      simp only [d234337, d235738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d234338 q = 1) (hb : d235739 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234338, d235739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234338, d235739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234339 q = 1) (hb : d235740 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234339, d235740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234339, d235740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234340 q = 1) (hb : d235741 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234340, d235741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234340, d235741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d234341 q = 1) (hb : d235742 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d234341, d235742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234341, d235742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234342 q = 1) (hb : d235743 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d234342, d235743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234342, d235743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro57270 (p : Pattern) (ha : d234348 p = 1) (hb : d235749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234343 q = 1) (hb : d235744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234343, d235744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57269 q ha hb
    | true =>
      simp only [d234343, d235744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234344 q = 1) (hb : d235745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234344, d235745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234344, d235745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234345 q = 1) (hb : d235746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234345, d235746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234345, d235746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234346 q = 1) (hb : d235747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234346, d235747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234346, d235747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234347 q = 1) (hb : d235748 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234347, d235748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234347, d235748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234348 q = 1) (hb : d235749 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234348, d235749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234348, d235749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57271 (p : Pattern) (ha : d234354 p = 1) (hb : d235755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234323 q = 1) (hb : d235735 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234323, d235735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57265 q ha hb
    | true =>
      simp only [d234323, d235735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57267 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234329 q = 1) (hb : d235736 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234329, d235736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234329, d235736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d234349 q = 1) (hb : d235750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234349, d235750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57270 q ha hb
    | true =>
      simp only [d234349, d235750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234350 q = 1) (hb : d235751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234350, d235751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234350, d235751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234351 q = 1) (hb : d235752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234351, d235752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234351, d235752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234352 q = 1) (hb : d235753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234352, d235753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234352, d235753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234353 q = 1) (hb : d235754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234353, d235754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234353, d235754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234354 q = 1) (hb : d235755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234354, d235755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234354, d235755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro57272 (p : Pattern) (ha : d234327 p = 1) (hb : d235760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234317 q = 1) (hb : d235729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234317, d235729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57266 q ha hb
    | true =>
      simp only [d234317, d235729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234318 q = 1) (hb : d235730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234318, d235730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234318, d235730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234324 q = 1) (hb : d235757 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234324, d235757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234324, d235757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234325 q = 1) (hb : d235758 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234325, d235758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234325, d235758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234326 q = 1) (hb : d235759 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234326, d235759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234326, d235759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234327 q = 1) (hb : d235760 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234327, d235760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234327, d235760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57273 (p : Pattern) (ha : d234361 p = 1) (hb : d235766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234356 q = 1) (hb : d235761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234356, d235761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57272 q ha hb
    | true =>
      simp only [d234356, d235761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234357 q = 1) (hb : d235762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234357, d235762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234357, d235762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234358 q = 1) (hb : d235763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234358, d235763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234358, d235763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234359 q = 1) (hb : d235764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234359, d235764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234359, d235764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234360 q = 1) (hb : d235765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234360, d235765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234360, d235765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234361 q = 1) (hb : d235766 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234361, d235766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234361, d235766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57274 (p : Pattern) (ha : d234367 p = 1) (hb : d235772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234140 q = 1) (hb : d235561 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234140, d235561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234140, d235561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57232 q ha hb
  have h2 (q : Pattern) (ha : d234141 q = 1) (hb : d235562 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234141, d235562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234141, d235562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234150 q = 1) (hb : d235571 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234150, d235571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57232 q ha hb
    | true =>
      simp only [d234150, d235571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57235 q ha hb
  have h4 (q : Pattern) (ha : d234151 q = 1) (hb : d235572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234151, d235572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234151, d235572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234152 q = 1) (hb : d235573 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234152, d235573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234152, d235573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234240 q = 1) (hb : d235652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234240, d235652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57247 q ha hb
    | true =>
      simp only [d234240, d235652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57254 q ha hb
  have h7 (q : Pattern) (ha : d234253 q = 1) (hb : d235665 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234253, d235665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57255 q ha hb
    | true =>
      simp only [d234253, d235665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57256 q ha hb
  have h8 (q : Pattern) (ha : d234254 q = 1) (hb : d235666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234254, d235666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234254, d235666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234255 q = 1) (hb : d235667 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234255, d235667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234255, d235667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d234256 q = 1) (hb : d235668 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234256, d235668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234256, d235668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234260 q = 1) (hb : d235672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234260, d235672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234260, d235672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57257 q ha hb
  have h12 (q : Pattern) (ha : d234262 q = 1) (hb : d235674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234262, d235674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234262, d235674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57258 q ha hb
  have h13 (q : Pattern) (ha : d234263 q = 1) (hb : d235675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234263, d235675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234263, d235675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234264 q = 1) (hb : d235676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234264, d235676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234264, d235676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d234265 q = 1) (hb : d235677 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234265, d235677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d234265, d235677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d234266 q = 1) (hb : d235678 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d234266, d235678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d234266, d235678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d234355 q = 1) (hb : d235756 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234355, d235756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234355, d235756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57271 q ha hb
  have h18 (q : Pattern) (ha : d234362 q = 1) (hb : d235767 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234362, d235767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234362, d235767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57273 q ha hb
  have h19 (q : Pattern) (ha : d234363 q = 1) (hb : d235768 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234363, d235768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d234363, d235768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d234364 q = 1) (hb : d235769 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234364, d235769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d234364, d235769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d234365 q = 1) (hb : d235770 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234365, d235770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d234365, d235770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d234366 q = 1) (hb : d235771 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d234366, d235771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d234366, d235771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d234367 q = 1) (hb : d235772 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d234367, d235772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d234367, d235772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro57275 (p : Pattern) (ha : d234373 p = 1) (hb : d235778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234368 q = 1) (hb : d235773 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d234368, d235773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234368, d235773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57274 q ha hb
  have h2 (q : Pattern) (ha : d234369 q = 1) (hb : d235774 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d234369, d235774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234369, d235774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234370 q = 1) (hb : d235775 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d234370, d235775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234370, d235775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234371 q = 1) (hb : d235776 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d234371, d235776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234371, d235776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234372 q = 1) (hb : d235777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d234372, d235777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234372, d235777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234373 q = 1) (hb : d235778 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d234373, d235778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234373, d235778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57276 (p : Pattern) (ha : d2028 p = 1) (hb : d53318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53293 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1997 q = 1) (hb : d53276 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2013 q = 1) (hb : d53292 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2027 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2027, d53306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2027, d53306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2028 q = 1) (hb : d53318 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2028, d53318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2028, d53318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro57277 (p : Pattern) (ha : d234386 p = 1) (hb : d235785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d234379 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2029 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57276 q ha hb
    | true =>
      simp only [d2029, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2030 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2030, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27032 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53323 q = 1) (hb : d235783 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d235783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d235783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d234385 q = 1) (hb : d235784 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d234385, d235784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234385, d235784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d234386 q = 1) (hb : d235785 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d234386, d235785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234386, d235785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57278 (p : Pattern) (ha : d234393 p = 1) (hb : d235793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2029 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57276 q ha hb
    | true =>
      simp only [d2029, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2030 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2030, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27032 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53323 q = 1) (hb : d235783 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d235783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d235783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d234385 q = 1) (hb : d235784 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d234385, d235784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234385, d235784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h11 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h12 (q : Pattern) (ha : d2061 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h13 (q : Pattern) (ha : d53327 q = 1) (hb : d235791 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d235791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d235791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d234392 q = 1) (hb : d235792 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d234392, d235792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234392, d235792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h15 (q : Pattern) (ha : d234393 q = 1) (hb : d235793 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d234393, d235793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234393, d235793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro57279 (p : Pattern) (ha : d234399 p = 1) (hb : d235799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d234384 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d234387 q = 1) (hb : d235786 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57277 q ha hb
    | true =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d234388 q = 1) (hb : d235787 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d234389 q = 1) (hb : d235788 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234389, d235788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234389, d235788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234390 q = 1) (hb : d235789 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234390, d235789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234390, d235789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d234391 q = 1) (hb : d235790 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234391, d235790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234391, d235790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234394 q = 1) (hb : d235794 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57278 q ha hb
    | true =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d234395 q = 1) (hb : d235795 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d234396 q = 1) (hb : d235796 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234396, d235796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234396, d235796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234397 q = 1) (hb : d235797 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234397, d235797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234397, d235797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d234398 q = 1) (hb : d235798 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234398, d235798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234398, d235798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234399 q = 1) (hb : d235799 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234399, d235799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234399, d235799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro57280 (p : Pattern) (ha : d234401 p = 1) (hb : d235801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234387 q = 1) (hb : d235786 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57277 q ha hb
    | true =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234388 q = 1) (hb : d235787 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234389 q = 1) (hb : d235788 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234389, d235788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234389, d235788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234390 q = 1) (hb : d235789 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234390, d235789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234390, d235789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234394 q = 1) (hb : d235794 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57278 q ha hb
    | true =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234395 q = 1) (hb : d235795 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234396 q = 1) (hb : d235796 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234396, d235796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234396, d235796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234397 q = 1) (hb : d235797 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234397, d235797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234397, d235797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234398 q = 1) (hb : d235798 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234398, d235798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234398, d235798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234400 q = 1) (hb : d235800 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234400, d235800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234400, d235800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d234401 q = 1) (hb : d235801 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234401, d235801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234401, d235801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro57281 (p : Pattern) (ha : d234405 p = 1) (hb : d235805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234394 q = 1) (hb : d235794 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57278 q ha hb
    | true =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234395 q = 1) (hb : d235795 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234396 q = 1) (hb : d235796 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234396, d235796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234396, d235796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234397 q = 1) (hb : d235797 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234397, d235797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234397, d235797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234400 q = 1) (hb : d235800 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234400, d235800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234400, d235800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234405 q = 1) (hb : d235805 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234405, d235805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234405, d235805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57282 (p : Pattern) (ha : d234412 p = 1) (hb : d235812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234402 q = 1) (hb : d235802 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234402, d235802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57279 q ha hb
    | true =>
      simp only [d234402, d235802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57280 q ha hb
  have h2 (q : Pattern) (ha : d234403 q = 1) (hb : d235803 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234403, d235803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234403, d235803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234404 q = 1) (hb : d235804 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234404, d235804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234404, d235804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234406 q = 1) (hb : d235806 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234406, d235806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57280 q ha hb
    | true =>
      simp only [d234406, d235806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57281 q ha hb
  have h5 (q : Pattern) (ha : d234407 q = 1) (hb : d235807 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234407, d235807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234407, d235807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234408 q = 1) (hb : d235808 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234408, d235808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234408, d235808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234409 q = 1) (hb : d235809 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234409, d235809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234409, d235809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234410 q = 1) (hb : d235810 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234410, d235810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234410, d235810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234411 q = 1) (hb : d235811 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d234411, d235811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234411, d235811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234412 q = 1) (hb : d235812 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d234412, d235812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234412, d235812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro57283 (p : Pattern) (ha : d234416 p = 1) (hb : d235816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234406 q = 1) (hb : d235806 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234406, d235806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57280 q ha hb
    | true =>
      simp only [d234406, d235806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57281 q ha hb
  have h2 (q : Pattern) (ha : d234407 q = 1) (hb : d235807 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234407, d235807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234407, d235807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234408 q = 1) (hb : d235808 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234408, d235808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234408, d235808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234410 q = 1) (hb : d235810 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234410, d235810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234410, d235810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234415 q = 1) (hb : d235815 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d234415, d235815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234415, d235815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234416 q = 1) (hb : d235816 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d234416, d235816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234416, d235816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57284 (p : Pattern) (ha : d234422 p = 1) (hb : d235822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234413 q = 1) (hb : d235813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57282 q ha hb
    | true =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234414 q = 1) (hb : d235814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234417 q = 1) (hb : d235817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57283 q ha hb
    | true =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234418 q = 1) (hb : d235818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234419 q = 1) (hb : d235819 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234419, d235819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234419, d235819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234420 q = 1) (hb : d235820 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234420, d235820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234420, d235820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234421 q = 1) (hb : d235821 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234421, d235821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234421, d235821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234422 q = 1) (hb : d235822 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234422, d235822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234422, d235822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57285 (p : Pattern) (ha : d234426 p = 1) (hb : d235826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234417 q = 1) (hb : d235817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57283 q ha hb
    | true =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234418 q = 1) (hb : d235818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234423 q = 1) (hb : d235823 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234423, d235823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234423, d235823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234424 q = 1) (hb : d235824 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234424, d235824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234424, d235824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234425 q = 1) (hb : d235825 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234425, d235825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234425, d235825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234426 q = 1) (hb : d235826 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234426, d235826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234426, d235826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57286 (p : Pattern) (ha : d234432 p = 1) (hb : d235832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234427 q = 1) (hb : d235827 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234427, d235827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57284 q ha hb
    | true =>
      simp only [d234427, d235827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57285 q ha hb
  have h2 (q : Pattern) (ha : d234428 q = 1) (hb : d235828 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234428, d235828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234428, d235828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234429 q = 1) (hb : d235829 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234429, d235829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234429, d235829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234430 q = 1) (hb : d235830 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234430, d235830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234430, d235830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234431 q = 1) (hb : d235831 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234431, d235831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234431, d235831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234432 q = 1) (hb : d235832 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234432, d235832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234432, d235832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57287 (p : Pattern) (ha : d234435 p = 1) (hb : d235835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234413 q = 1) (hb : d235813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57282 q ha hb
    | true =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234414 q = 1) (hb : d235814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234417 q = 1) (hb : d235817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57283 q ha hb
    | true =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234418 q = 1) (hb : d235818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234419 q = 1) (hb : d235819 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234419, d235819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234419, d235819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234420 q = 1) (hb : d235820 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234420, d235820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234420, d235820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234421 q = 1) (hb : d235821 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234421, d235821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234421, d235821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234435 q = 1) (hb : d235835 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234435, d235835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234435, d235835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro57288 (p : Pattern) (ha : d234436 p = 1) (hb : d235836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234417 q = 1) (hb : d235817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57283 q ha hb
    | true =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234418 q = 1) (hb : d235818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234423 q = 1) (hb : d235823 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234423, d235823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234423, d235823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234424 q = 1) (hb : d235824 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234424, d235824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234424, d235824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234425 q = 1) (hb : d235825 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234425, d235825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234425, d235825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234436 q = 1) (hb : d235836 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234436, d235836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234436, d235836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57289 (p : Pattern) (ha : d234442 p = 1) (hb : d235842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234427 q = 1) (hb : d235827 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234427, d235827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57284 q ha hb
    | true =>
      simp only [d234427, d235827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57285 q ha hb
  have h2 (q : Pattern) (ha : d234428 q = 1) (hb : d235828 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234428, d235828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234428, d235828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234429 q = 1) (hb : d235829 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234429, d235829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234429, d235829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234430 q = 1) (hb : d235830 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234430, d235830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234430, d235830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234431 q = 1) (hb : d235831 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234431, d235831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234431, d235831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234437 q = 1) (hb : d235837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234437, d235837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57287 q ha hb
    | true =>
      simp only [d234437, d235837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57288 q ha hb
  have h7 (q : Pattern) (ha : d234438 q = 1) (hb : d235838 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234438, d235838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234438, d235838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234439 q = 1) (hb : d235839 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234439, d235839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234439, d235839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234440 q = 1) (hb : d235840 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234440, d235840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234440, d235840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234441 q = 1) (hb : d235841 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234441, d235841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234441, d235841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234442 q = 1) (hb : d235842 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234442, d235842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234442, d235842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro57290 (p : Pattern) (ha : d234447 p = 1) (hb : d235847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234413 q = 1) (hb : d235813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57282 q ha hb
    | true =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234414 q = 1) (hb : d235814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234417 q = 1) (hb : d235817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57283 q ha hb
    | true =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234418 q = 1) (hb : d235818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234419 q = 1) (hb : d235819 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234419, d235819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234419, d235819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234420 q = 1) (hb : d235820 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234420, d235820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234420, d235820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234446 q = 1) (hb : d235846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234446, d235846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234446, d235846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234447 q = 1) (hb : d235847 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234447, d235847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234447, d235847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57291 (p : Pattern) (ha : d234449 p = 1) (hb : d235849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234417 q = 1) (hb : d235817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57283 q ha hb
    | true =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234418 q = 1) (hb : d235818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234423 q = 1) (hb : d235823 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234423, d235823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234423, d235823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234424 q = 1) (hb : d235824 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234424, d235824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234424, d235824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234448 q = 1) (hb : d235848 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234448, d235848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234448, d235848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234449 q = 1) (hb : d235849 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234449, d235849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234449, d235849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57292 (p : Pattern) (ha : d234456 p = 1) (hb : d235856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234413 q = 1) (hb : d235813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57282 q ha hb
    | true =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234414 q = 1) (hb : d235814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234417 q = 1) (hb : d235817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57283 q ha hb
    | true =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234418 q = 1) (hb : d235818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234419 q = 1) (hb : d235819 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234419, d235819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234419, d235819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234454 q = 1) (hb : d235854 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234454, d235854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234454, d235854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234455 q = 1) (hb : d235855 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234455, d235855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234455, d235855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234456 q = 1) (hb : d235856 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234456, d235856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234456, d235856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57293 (p : Pattern) (ha : d234459 p = 1) (hb : d235859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234417 q = 1) (hb : d235817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57283 q ha hb
    | true =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234418 q = 1) (hb : d235818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234423 q = 1) (hb : d235823 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234423, d235823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234423, d235823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234457 q = 1) (hb : d235857 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234457, d235857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234457, d235857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234458 q = 1) (hb : d235858 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234458, d235858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234458, d235858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234459 q = 1) (hb : d235859 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234459, d235859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234459, d235859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57294 (p : Pattern) (ha : d234469 p = 1) (hb : d235863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d234468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234384 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234387 q = 1) (hb : d235786 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57277 q ha hb
    | true =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d234388 q = 1) (hb : d235787 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d234389 q = 1) (hb : d235788 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234389, d235788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d234389, d235788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234390 q = 1) (hb : d235789 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234390, d235789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234390, d235789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d234391 q = 1) (hb : d235790 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234391, d235790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234391, d235790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234469 q = 1) (hb : d235863 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234469, d235863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234469, d235863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57295 (p : Pattern) (ha : d234475 p = 1) (hb : d235869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234470 q = 1) (hb : d235864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234470, d235864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57294 q ha hb
    | true =>
      simp only [d234470, d235864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57279 q ha hb
  have h2 (q : Pattern) (ha : d234471 q = 1) (hb : d235865 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234471, d235865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234471, d235865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234472 q = 1) (hb : d235866 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234472, d235866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234472, d235866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234402 q = 1) (hb : d235802 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234402, d235802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57279 q ha hb
    | true =>
      simp only [d234402, d235802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57280 q ha hb
  have h5 (q : Pattern) (ha : d234403 q = 1) (hb : d235803 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234403, d235803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234403, d235803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234404 q = 1) (hb : d235804 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234404, d235804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234404, d235804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234473 q = 1) (hb : d235867 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234473, d235867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234473, d235867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234406 q = 1) (hb : d235806 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234406, d235806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57280 q ha hb
    | true =>
      simp only [d234406, d235806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57281 q ha hb
  have h9 (q : Pattern) (ha : d234407 q = 1) (hb : d235807 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234407, d235807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234407, d235807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234408 q = 1) (hb : d235808 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234408, d235808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234408, d235808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234409 q = 1) (hb : d235809 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234409, d235809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234409, d235809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234474 q = 1) (hb : d235868 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d234474, d235868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234474, d235868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234475 q = 1) (hb : d235869 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d234475, d235869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d234475, d235869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro57296 (p : Pattern) (ha : d234481 p = 1) (hb : d235875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234476 q = 1) (hb : d235870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234476, d235870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57295 q ha hb
    | true =>
      simp only [d234476, d235870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234477 q = 1) (hb : d235871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234477, d235871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234477, d235871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234413 q = 1) (hb : d235813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57282 q ha hb
    | true =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234414 q = 1) (hb : d235814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234478 q = 1) (hb : d235872 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234478, d235872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234478, d235872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234479 q = 1) (hb : d235873 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234479, d235873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234479, d235873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234480 q = 1) (hb : d235874 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234480, d235874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234480, d235874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234481 q = 1) (hb : d235875 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234481, d235875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234481, d235875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57297 (p : Pattern) (ha : d234490 p = 1) (hb : d235878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234387 q = 1) (hb : d235786 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57277 q ha hb
    | true =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234388 q = 1) (hb : d235787 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234389 q = 1) (hb : d235788 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234389, d235788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234389, d235788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234390 q = 1) (hb : d235789 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234390, d235789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234390, d235789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234394 q = 1) (hb : d235794 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57278 q ha hb
    | true =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234395 q = 1) (hb : d235795 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234396 q = 1) (hb : d235796 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234396, d235796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234396, d235796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234397 q = 1) (hb : d235797 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234397, d235797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234397, d235797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234398 q = 1) (hb : d235798 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234398, d235798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234398, d235798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d234489 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d234490 q = 1) (hb : d235878 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234490, d235878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234490, d235878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro57298 (p : Pattern) (ha : d234497 p = 1) (hb : d235884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234402 q = 1) (hb : d235802 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234402, d235802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57279 q ha hb
    | true =>
      simp only [d234402, d235802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57280 q ha hb
  have h2 (q : Pattern) (ha : d234403 q = 1) (hb : d235803 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234403, d235803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234403, d235803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234404 q = 1) (hb : d235804 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234404, d235804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234404, d235804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234406 q = 1) (hb : d235806 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234406, d235806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57280 q ha hb
    | true =>
      simp only [d234406, d235806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57281 q ha hb
  have h5 (q : Pattern) (ha : d234407 q = 1) (hb : d235807 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234407, d235807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234407, d235807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234408 q = 1) (hb : d235808 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234408, d235808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234408, d235808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234409 q = 1) (hb : d235809 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234409, d235809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234409, d235809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d234491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d234492 q = 1) (hb : d235879 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234492, d235879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57297 q ha hb
    | true =>
      simp only [d234492, d235879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d234493 q = 1) (hb : d235880 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234493, d235880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234493, d235880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234494 q = 1) (hb : d235881 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234494, d235881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234494, d235881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234495 q = 1) (hb : d235882 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234495, d235882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234495, d235882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d234496 q = 1) (hb : d235883 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d234496, d235883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234496, d235883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234497 q = 1) (hb : d235884 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d234497, d235884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234497, d235884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro57299 (p : Pattern) (ha : d234503 p = 1) (hb : d235890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234498 q = 1) (hb : d235885 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234498, d235885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57298 q ha hb
    | true =>
      simp only [d234498, d235885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234499 q = 1) (hb : d235886 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234499, d235886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234499, d235886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234500 q = 1) (hb : d235887 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234500, d235887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234500, d235887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234501 q = 1) (hb : d235888 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234501, d235888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234501, d235888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234502 q = 1) (hb : d235889 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234502, d235889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234502, d235889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234503 q = 1) (hb : d235890 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234503, d235890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234503, d235890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57300 (p : Pattern) (ha : d234509 p = 1) (hb : d235896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234450 q = 1) (hb : d235850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234450, d235850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57290 q ha hb
    | true =>
      simp only [d234450, d235850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57291 q ha hb
  have h2 (q : Pattern) (ha : d234451 q = 1) (hb : d235851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234451, d235851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234451, d235851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234452 q = 1) (hb : d235852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234452, d235852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234452, d235852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234453 q = 1) (hb : d235853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234453, d235853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234453, d235853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234460 q = 1) (hb : d235860 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234460, d235860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57292 q ha hb
    | true =>
      simp only [d234460, d235860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57293 q ha hb
  have h6 (q : Pattern) (ha : d234461 q = 1) (hb : d235861 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234461, d235861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234461, d235861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234462 q = 1) (hb : d235862 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234462, d235862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234462, d235862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234482 q = 1) (hb : d235876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234482, d235876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57296 q ha hb
    | true =>
      simp only [d234482, d235876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57284 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d234427 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d234483 q = 1) (hb : d235877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234483, d235877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234483, d235877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d234504 q = 1) (hb : d235891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234504, d235891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57299 q ha hb
    | true =>
      simp only [d234504, d235891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d234505 q = 1) (hb : d235892 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234505, d235892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234505, d235892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d234506 q = 1) (hb : d235893 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234506, d235893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d234506, d235893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234507 q = 1) (hb : d235894 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234507, d235894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234507, d235894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d234508 q = 1) (hb : d235895 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234508, d235895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234508, d235895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d234509 q = 1) (hb : d235896 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234509, d235896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234509, d235896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro57301 (p : Pattern) (ha : d234510 p = 1) (hb : d235897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234413 q = 1) (hb : d235813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57282 q ha hb
    | true =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234414 q = 1) (hb : d235814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234417 q = 1) (hb : d235817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57283 q ha hb
    | true =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234418 q = 1) (hb : d235818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234419 q = 1) (hb : d235819 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234419, d235819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234419, d235819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234420 q = 1) (hb : d235820 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234420, d235820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234420, d235820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234446 q = 1) (hb : d235846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234446, d235846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234446, d235846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234510 q = 1) (hb : d235897 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234510, d235897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234510, d235897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro57302 (p : Pattern) (ha : d234511 p = 1) (hb : d235898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234417 q = 1) (hb : d235817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57283 q ha hb
    | true =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234418 q = 1) (hb : d235818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234423 q = 1) (hb : d235823 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234423, d235823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234423, d235823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234424 q = 1) (hb : d235824 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234424, d235824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234424, d235824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234448 q = 1) (hb : d235848 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234448, d235848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234448, d235848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234511 q = 1) (hb : d235898 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234511, d235898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234511, d235898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57303 (p : Pattern) (ha : d234516 p = 1) (hb : d235903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234413 q = 1) (hb : d235813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57282 q ha hb
    | true =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234414 q = 1) (hb : d235814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234417 q = 1) (hb : d235817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57283 q ha hb
    | true =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234418 q = 1) (hb : d235818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234419 q = 1) (hb : d235819 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234419, d235819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234419, d235819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234454 q = 1) (hb : d235854 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234454, d235854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234454, d235854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234455 q = 1) (hb : d235855 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234455, d235855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234455, d235855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234516 q = 1) (hb : d235903 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234516, d235903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234516, d235903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro57304 (p : Pattern) (ha : d234517 p = 1) (hb : d235904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234417 q = 1) (hb : d235817 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57283 q ha hb
    | true =>
      simp only [d234417, d235817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234418 q = 1) (hb : d235818 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234418, d235818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234423 q = 1) (hb : d235823 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234423, d235823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234423, d235823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234457 q = 1) (hb : d235857 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234457, d235857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234457, d235857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234458 q = 1) (hb : d235858 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234458, d235858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234458, d235858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234517 q = 1) (hb : d235904 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234517, d235904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234517, d235904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57305 (p : Pattern) (ha : d234521 p = 1) (hb : d235908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234476 q = 1) (hb : d235870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234476, d235870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57295 q ha hb
    | true =>
      simp only [d234476, d235870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234477 q = 1) (hb : d235871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234477, d235871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234477, d235871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234413 q = 1) (hb : d235813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57282 q ha hb
    | true =>
      simp only [d234413, d235813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234414 q = 1) (hb : d235814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234414, d235814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234478 q = 1) (hb : d235872 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234478, d235872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234478, d235872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234479 q = 1) (hb : d235873 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234479, d235873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234479, d235873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234480 q = 1) (hb : d235874 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234480, d235874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234480, d235874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234521 q = 1) (hb : d235908 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234521, d235908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234521, d235908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro57306 (p : Pattern) (ha : d234524 p = 1) (hb : d235911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234498 q = 1) (hb : d235885 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234498, d235885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57298 q ha hb
    | true =>
      simp only [d234498, d235885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234499 q = 1) (hb : d235886 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234499, d235886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234499, d235886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234500 q = 1) (hb : d235887 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234500, d235887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234500, d235887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234501 q = 1) (hb : d235888 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234501, d235888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234501, d235888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234502 q = 1) (hb : d235889 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234502, d235889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234502, d235889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234524 q = 1) (hb : d235911 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234524, d235911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234524, d235911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57307 (p : Pattern) (ha : d234530 p = 1) (hb : d235917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234450 q = 1) (hb : d235850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234450, d235850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57290 q ha hb
    | true =>
      simp only [d234450, d235850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57291 q ha hb
  have h2 (q : Pattern) (ha : d234451 q = 1) (hb : d235851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234451, d235851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234451, d235851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234452 q = 1) (hb : d235852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234452, d235852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234452, d235852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234453 q = 1) (hb : d235853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234453, d235853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234453, d235853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234460 q = 1) (hb : d235860 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234460, d235860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57292 q ha hb
    | true =>
      simp only [d234460, d235860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57293 q ha hb
  have h6 (q : Pattern) (ha : d234461 q = 1) (hb : d235861 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234461, d235861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234461, d235861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234462 q = 1) (hb : d235862 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234462, d235862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234462, d235862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234482 q = 1) (hb : d235876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234482, d235876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57296 q ha hb
    | true =>
      simp only [d234482, d235876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57284 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d234427 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d234483 q = 1) (hb : d235877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234483, d235877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234483, d235877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d234504 q = 1) (hb : d235891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234504, d235891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57299 q ha hb
    | true =>
      simp only [d234504, d235891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d234505 q = 1) (hb : d235892 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234505, d235892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234505, d235892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d234506 q = 1) (hb : d235893 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234506, d235893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d234506, d235893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234507 q = 1) (hb : d235894 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234507, d235894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234507, d235894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d234508 q = 1) (hb : d235895 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234508, d235895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234508, d235895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d234512 q = 1) (hb : d235899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234512, d235899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57301 q ha hb
    | true =>
      simp only [d234512, d235899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57302 q ha hb
  have h17 (q : Pattern) (ha : d234513 q = 1) (hb : d235900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234513, d235900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234513, d235900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d234514 q = 1) (hb : d235901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234514, d235901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d234514, d235901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d234515 q = 1) (hb : d235902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234515, d235902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234515, d235902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d234518 q = 1) (hb : d235905 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234518, d235905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57303 q ha hb
    | true =>
      simp only [d234518, d235905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57304 q ha hb
  have h21 (q : Pattern) (ha : d234519 q = 1) (hb : d235906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234519, d235906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234519, d235906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d234520 q = 1) (hb : d235907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234520, d235907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d234520, d235907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d234522 q = 1) (hb : d235909 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234522, d235909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57305 q ha hb
    | true =>
      simp only [d234522, d235909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57287 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d234437 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d234523 q = 1) (hb : d235910 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234523, d235910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d234523, d235910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d234525 q = 1) (hb : d235912 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234525, d235912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57306 q ha hb
    | true =>
      simp only [d234525, d235912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d234526 q = 1) (hb : d235913 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234526, d235913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d234526, d235913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d234527 q = 1) (hb : d235914 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234527, d235914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d234527, d235914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d234528 q = 1) (hb : d235915 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234528, d235915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d234528, d235915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d234529 q = 1) (hb : d235916 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234529, d235916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d234529, d235916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d234530 q = 1) (hb : d235917 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234530, d235917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d234530, d235917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro57308 (p : Pattern) (ha : d234537 p = 1) (hb : d235924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234427 q = 1) (hb : d235827 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234427, d235827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57284 q ha hb
    | true =>
      simp only [d234427, d235827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57285 q ha hb
  have h2 (q : Pattern) (ha : d234428 q = 1) (hb : d235828 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234428, d235828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234428, d235828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234429 q = 1) (hb : d235829 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234429, d235829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234429, d235829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234430 q = 1) (hb : d235830 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234430, d235830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234430, d235830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234431 q = 1) (hb : d235831 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234431, d235831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234431, d235831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234532 q = 1) (hb : d235919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234532, d235919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57285 q ha hb
    | true =>
      simp only [d234532, d235919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234533 q = 1) (hb : d235920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234533, d235920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234533, d235920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234534 q = 1) (hb : d235921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234534, d235921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234534, d235921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234535 q = 1) (hb : d235922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234535, d235922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234535, d235922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234536 q = 1) (hb : d235923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234536, d235923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234536, d235923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234537 q = 1) (hb : d235924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234537, d235924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234537, d235924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro57309 (p : Pattern) (ha : d234543 p = 1) (hb : d235930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234532 q = 1) (hb : d235919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234532, d235919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57285 q ha hb
    | true =>
      simp only [d234532, d235919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234533 q = 1) (hb : d235920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234533, d235920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234533, d235920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234534 q = 1) (hb : d235921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234534, d235921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234534, d235921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234535 q = 1) (hb : d235922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234535, d235922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234535, d235922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234536 q = 1) (hb : d235923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234536, d235923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234536, d235923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234538 q = 1) (hb : d235925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234538, d235925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57288 q ha hb
    | true =>
      simp only [d234538, d235925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234539 q = 1) (hb : d235926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234539, d235926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234539, d235926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234540 q = 1) (hb : d235927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234540, d235927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234540, d235927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234541 q = 1) (hb : d235928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234541, d235928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234541, d235928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234542 q = 1) (hb : d235929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234542, d235929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234542, d235929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234543 q = 1) (hb : d235930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234543, d235930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234543, d235930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro57310 (p : Pattern) (ha : d234550 p = 1) (hb : d235937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234522 q = 1) (hb : d235909 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234522, d235909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57305 q ha hb
    | true =>
      simp only [d234522, d235909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57287 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234437 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234523 q = 1) (hb : d235910 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234523, d235910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234523, d235910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d234525 q = 1) (hb : d235912 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234525, d235912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57306 q ha hb
    | true =>
      simp only [d234525, d235912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234526 q = 1) (hb : d235913 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234526, d235913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234526, d235913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234527 q = 1) (hb : d235914 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234527, d235914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234527, d235914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234548 q = 1) (hb : d235935 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234548, d235935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234548, d235935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234549 q = 1) (hb : d235936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234549, d235936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234549, d235936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234550 q = 1) (hb : d235937 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234550, d235937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234550, d235937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro57311 (p : Pattern) (ha : d234552 p = 1) (hb : d235939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234538 q = 1) (hb : d235925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234538, d235925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57288 q ha hb
    | true =>
      simp only [d234538, d235925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234539 q = 1) (hb : d235926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234539, d235926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234539, d235926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234540 q = 1) (hb : d235927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234540, d235927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234540, d235927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234541 q = 1) (hb : d235928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234541, d235928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234541, d235928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234542 q = 1) (hb : d235929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234542, d235929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234542, d235929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234552 q = 1) (hb : d235939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234552, d235939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234552, d235939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57312 (p : Pattern) (ha : d234572 p = 1) (hb : d235950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d234566 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234565 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234567 q = 1) (hb : d235945 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234567, d235945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d234567, d235945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57277 q ha hb
  have h4 (q : Pattern) (ha : d234387 q = 1) (hb : d235786 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57277 q ha hb
    | true =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d234568 q = 1) (hb : d235946 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234568, d235946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234568, d235946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234388 q = 1) (hb : d235787 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d234569 q = 1) (hb : d235947 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234569, d235947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234569, d235947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234570 q = 1) (hb : d235948 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234570, d235948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234570, d235948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d234571 q = 1) (hb : d235949 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234571, d235949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234571, d235949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234572 q = 1) (hb : d235950 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234572, d235950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234572, d235950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57313 (p : Pattern) (ha : d234578 p = 1) (hb : d235956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d234565 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d234567 q = 1) (hb : d235945 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234567, d235945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234567, d235945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57277 q ha hb
  have h3 (q : Pattern) (ha : d234387 q = 1) (hb : d235786 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57277 q ha hb
    | true =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d234568 q = 1) (hb : d235946 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234568, d235946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234568, d235946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234388 q = 1) (hb : d235787 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d234569 q = 1) (hb : d235947 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234569, d235947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234569, d235947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234570 q = 1) (hb : d235948 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234570, d235948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234570, d235948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d234571 q = 1) (hb : d235949 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234571, d235949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234571, d235949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234573 q = 1) (hb : d235951 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234573, d235951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234573, d235951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57278 q ha hb
  have h10 (q : Pattern) (ha : d234394 q = 1) (hb : d235794 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57278 q ha hb
    | true =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d234574 q = 1) (hb : d235952 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234574, d235952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234574, d235952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234395 q = 1) (hb : d235795 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d234575 q = 1) (hb : d235953 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234575, d235953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234575, d235953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234576 q = 1) (hb : d235954 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234576, d235954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234576, d235954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d234577 q = 1) (hb : d235955 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234577, d235955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234577, d235955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d234578 q = 1) (hb : d235956 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234578, d235956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234578, d235956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro57314 (p : Pattern) (ha : d234583 p = 1) (hb : d235961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234567 q = 1) (hb : d235945 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234567, d235945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234567, d235945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57277 q ha hb
  have h2 (q : Pattern) (ha : d234387 q = 1) (hb : d235786 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57277 q ha hb
    | true =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234568 q = 1) (hb : d235946 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234568, d235946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234568, d235946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234388 q = 1) (hb : d235787 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234569 q = 1) (hb : d235947 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234569, d235947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234569, d235947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234570 q = 1) (hb : d235948 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234570, d235948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234570, d235948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234573 q = 1) (hb : d235951 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234573, d235951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234573, d235951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57278 q ha hb
  have h8 (q : Pattern) (ha : d234394 q = 1) (hb : d235794 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57278 q ha hb
    | true =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234574 q = 1) (hb : d235952 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234574, d235952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234574, d235952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234395 q = 1) (hb : d235795 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d234575 q = 1) (hb : d235953 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234575, d235953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234575, d235953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234576 q = 1) (hb : d235954 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234576, d235954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234576, d235954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d234577 q = 1) (hb : d235955 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234577, d235955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234577, d235955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234582 q = 1) (hb : d235960 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234582, d235960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d234582, d235960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d234583 q = 1) (hb : d235961 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234583, d235961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234583, d235961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro57315 (p : Pattern) (ha : d234588 p = 1) (hb : d235966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234573 q = 1) (hb : d235951 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234573, d235951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234573, d235951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57278 q ha hb
  have h2 (q : Pattern) (ha : d234394 q = 1) (hb : d235794 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57278 q ha hb
    | true =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234574 q = 1) (hb : d235952 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234574, d235952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234574, d235952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234395 q = 1) (hb : d235795 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234575 q = 1) (hb : d235953 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234575, d235953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234575, d235953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234576 q = 1) (hb : d235954 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234576, d235954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234576, d235954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234582 q = 1) (hb : d235960 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234582, d235960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234582, d235960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234588 q = 1) (hb : d235966 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234588, d235966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234588, d235966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro57316 (p : Pattern) (ha : d234594 p = 1) (hb : d235972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234579 q = 1) (hb : d235957 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234579, d235957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57312 q ha hb
    | true =>
      simp only [d234579, d235957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57313 q ha hb
  have h2 (q : Pattern) (ha : d234580 q = 1) (hb : d235958 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234580, d235958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234580, d235958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234581 q = 1) (hb : d235959 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234581, d235959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234581, d235959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234584 q = 1) (hb : d235962 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234584, d235962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57313 q ha hb
    | true =>
      simp only [d234584, d235962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57314 q ha hb
  have h5 (q : Pattern) (ha : d234585 q = 1) (hb : d235963 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234585, d235963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234585, d235963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234586 q = 1) (hb : d235964 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234586, d235964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234586, d235964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234587 q = 1) (hb : d235965 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234587, d235965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234587, d235965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234589 q = 1) (hb : d235967 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234589, d235967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57314 q ha hb
    | true =>
      simp only [d234589, d235967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57315 q ha hb
  have h9 (q : Pattern) (ha : d234590 q = 1) (hb : d235968 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234590, d235968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234590, d235968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234591 q = 1) (hb : d235969 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234591, d235969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234591, d235969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234592 q = 1) (hb : d235970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234592, d235970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234592, d235970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234593 q = 1) (hb : d235971 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d234593, d235971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234593, d235971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234594 q = 1) (hb : d235972 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d234594, d235972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d234594, d235972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro57317 (p : Pattern) (ha : d234599 p = 1) (hb : d235977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234584 q = 1) (hb : d235962 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234584, d235962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57313 q ha hb
    | true =>
      simp only [d234584, d235962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57314 q ha hb
  have h2 (q : Pattern) (ha : d234585 q = 1) (hb : d235963 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234585, d235963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234585, d235963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234586 q = 1) (hb : d235964 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234586, d235964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234586, d235964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234589 q = 1) (hb : d235967 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234589, d235967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57314 q ha hb
    | true =>
      simp only [d234589, d235967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57315 q ha hb
  have h5 (q : Pattern) (ha : d234590 q = 1) (hb : d235968 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234590, d235968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234590, d235968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234591 q = 1) (hb : d235969 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234591, d235969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234591, d235969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234592 q = 1) (hb : d235970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234592, d235970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234592, d235970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234597 q = 1) (hb : d235975 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234597, d235975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234597, d235975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234598 q = 1) (hb : d235976 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d234598, d235976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234598, d235976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234599 q = 1) (hb : d235977 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d234599, d235977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234599, d235977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro57318 (p : Pattern) (ha : d234605 p = 1) (hb : d235983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234595 q = 1) (hb : d235973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234595, d235973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57316 q ha hb
    | true =>
      simp only [d234595, d235973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234596 q = 1) (hb : d235974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234596, d235974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234596, d235974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234600 q = 1) (hb : d235978 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234600, d235978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57317 q ha hb
    | true =>
      simp only [d234600, d235978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234601 q = 1) (hb : d235979 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234601, d235979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234601, d235979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234602 q = 1) (hb : d235980 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234602, d235980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234602, d235980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234603 q = 1) (hb : d235981 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234603, d235981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234603, d235981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234604 q = 1) (hb : d235982 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234604, d235982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234604, d235982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234605 q = 1) (hb : d235983 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234605, d235983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234605, d235983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro57319 (p : Pattern) (ha : d234607 p = 1) (hb : d235985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234589 q = 1) (hb : d235967 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234589, d235967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57314 q ha hb
    | true =>
      simp only [d234589, d235967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57315 q ha hb
  have h2 (q : Pattern) (ha : d234590 q = 1) (hb : d235968 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234590, d235968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234590, d235968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234591 q = 1) (hb : d235969 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234591, d235969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234591, d235969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234597 q = 1) (hb : d235975 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234597, d235975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234597, d235975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234606 q = 1) (hb : d235984 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d234606, d235984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234606, d235984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234607 q = 1) (hb : d235985 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d234607, d235985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234607, d235985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57320 (p : Pattern) (ha : d234613 p = 1) (hb : d235991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234600 q = 1) (hb : d235978 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234600, d235978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57317 q ha hb
    | true =>
      simp only [d234600, d235978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234601 q = 1) (hb : d235979 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234601, d235979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234601, d235979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234608 q = 1) (hb : d235986 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234608, d235986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57319 q ha hb
    | true =>
      simp only [d234608, d235986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234609 q = 1) (hb : d235987 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234609, d235987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234609, d235987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234610 q = 1) (hb : d235988 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234610, d235988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234610, d235988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234611 q = 1) (hb : d235989 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234611, d235989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234611, d235989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234612 q = 1) (hb : d235990 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234612, d235990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234612, d235990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d234613 q = 1) (hb : d235991 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234613, d235991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234613, d235991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro57321 (p : Pattern) (ha : d234626 p = 1) (hb : d235994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234567 q = 1) (hb : d235945 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234567, d235945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234567, d235945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57277 q ha hb
  have h2 (q : Pattern) (ha : d234387 q = 1) (hb : d235786 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57277 q ha hb
    | true =>
      simp only [d234387, d235786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234568 q = 1) (hb : d235946 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234568, d235946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234568, d235946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234388 q = 1) (hb : d235787 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234388, d235787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234569 q = 1) (hb : d235947 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234569, d235947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234569, d235947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234570 q = 1) (hb : d235948 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234570, d235948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234570, d235948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d234573 q = 1) (hb : d235951 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234573, d235951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234573, d235951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57278 q ha hb
  have h8 (q : Pattern) (ha : d234394 q = 1) (hb : d235794 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57278 q ha hb
    | true =>
      simp only [d234394, d235794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d234574 q = 1) (hb : d235952 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234574, d235952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234574, d235952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234395 q = 1) (hb : d235795 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234395, d235795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d234575 q = 1) (hb : d235953 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d234575, d235953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234575, d235953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234576 q = 1) (hb : d235954 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d234576, d235954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234576, d235954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d234577 q = 1) (hb : d235955 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d234577, d235955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234577, d235955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d234625 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d234626 q = 1) (hb : d235994 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d234626, d235994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234626, d235994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro57322 (p : Pattern) (ha : d234633 p = 1) (hb : d236000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234584 q = 1) (hb : d235962 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234584, d235962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57313 q ha hb
    | true =>
      simp only [d234584, d235962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57314 q ha hb
  have h2 (q : Pattern) (ha : d234585 q = 1) (hb : d235963 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234585, d235963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234585, d235963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234586 q = 1) (hb : d235964 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234586, d235964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234586, d235964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234589 q = 1) (hb : d235967 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234589, d235967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57314 q ha hb
    | true =>
      simp only [d234589, d235967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57315 q ha hb
  have h5 (q : Pattern) (ha : d234590 q = 1) (hb : d235968 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234590, d235968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234590, d235968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234591 q = 1) (hb : d235969 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234591, d235969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234591, d235969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234592 q = 1) (hb : d235970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234592, d235970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234592, d235970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d234627 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d234628 q = 1) (hb : d235995 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d234628, d235995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57321 q ha hb
    | true =>
      simp only [d234628, d235995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d234629 q = 1) (hb : d235996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d234629, d235996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234629, d235996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234630 q = 1) (hb : d235997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234630, d235997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234630, d235997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234631 q = 1) (hb : d235998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d234631, d235998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234631, d235998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d234632 q = 1) (hb : d235999 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d234632, d235999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234632, d235999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234633 q = 1) (hb : d236000 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d234633, d236000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234633, d236000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro57323 (p : Pattern) (ha : d234639 p = 1) (hb : d236006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234634 q = 1) (hb : d236001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234634, d236001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57322 q ha hb
    | true =>
      simp only [d234634, d236001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234635 q = 1) (hb : d236002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234635, d236002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234635, d236002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234636 q = 1) (hb : d236003 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234636, d236003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234636, d236003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234637 q = 1) (hb : d236004 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234637, d236004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234637, d236004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234638 q = 1) (hb : d236005 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234638, d236005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234638, d236005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234639 q = 1) (hb : d236006 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234639, d236006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234639, d236006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57324 (p : Pattern) (ha : d234645 p = 1) (hb : d236012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234614 q = 1) (hb : d235992 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234614, d235992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57318 q ha hb
    | true =>
      simp only [d234614, d235992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57320 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234619 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234620 q = 1) (hb : d235993 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234620, d235993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234620, d235993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d234640 q = 1) (hb : d236007 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234640, d236007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57323 q ha hb
    | true =>
      simp only [d234640, d236007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234641 q = 1) (hb : d236008 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234641, d236008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234641, d236008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234642 q = 1) (hb : d236009 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234642, d236009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234642, d236009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234643 q = 1) (hb : d236010 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234643, d236010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234643, d236010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234644 q = 1) (hb : d236011 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234644, d236011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234644, d236011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234645 q = 1) (hb : d236012 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234645, d236012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234645, d236012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro57325 (p : Pattern) (ha : d234618 p = 1) (hb : d236017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234608 q = 1) (hb : d235986 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d234608, d235986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57319 q ha hb
    | true =>
      simp only [d234608, d235986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234609 q = 1) (hb : d235987 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d234609, d235987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234609, d235987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234615 q = 1) (hb : d236014 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d234615, d236014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234615, d236014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234616 q = 1) (hb : d236015 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d234616, d236015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234616, d236015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234617 q = 1) (hb : d236016 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d234617, d236016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234617, d236016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234618 q = 1) (hb : d236017 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d234618, d236017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234618, d236017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57326 (p : Pattern) (ha : d234652 p = 1) (hb : d236023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234647 q = 1) (hb : d236018 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234647, d236018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57325 q ha hb
    | true =>
      simp only [d234647, d236018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234648 q = 1) (hb : d236019 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234648, d236019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234648, d236019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234649 q = 1) (hb : d236020 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234649, d236020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234649, d236020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234650 q = 1) (hb : d236021 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234650, d236021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234650, d236021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234651 q = 1) (hb : d236022 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234651, d236022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234651, d236022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234652 q = 1) (hb : d236023 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234652, d236023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234652, d236023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57327 (p : Pattern) (ha : d234658 p = 1) (hb : d236029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234433 q = 1) (hb : d235833 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234433, d235833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234433, d235833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57286 q ha hb
  have h2 (q : Pattern) (ha : d234434 q = 1) (hb : d235834 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234434, d235834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234434, d235834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234443 q = 1) (hb : d235843 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234443, d235843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57286 q ha hb
    | true =>
      simp only [d234443, d235843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57289 q ha hb
  have h4 (q : Pattern) (ha : d234444 q = 1) (hb : d235844 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234444, d235844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234444, d235844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234445 q = 1) (hb : d235845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234445, d235845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234445, d235845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234531 q = 1) (hb : d235918 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234531, d235918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57300 q ha hb
    | true =>
      simp only [d234531, d235918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57307 q ha hb
  have h7 (q : Pattern) (ha : d234544 q = 1) (hb : d235931 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234544, d235931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57308 q ha hb
    | true =>
      simp only [d234544, d235931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57309 q ha hb
  have h8 (q : Pattern) (ha : d234545 q = 1) (hb : d235932 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234545, d235932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234545, d235932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234546 q = 1) (hb : d235933 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234546, d235933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234546, d235933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d234547 q = 1) (hb : d235934 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234547, d235934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234547, d235934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234551 q = 1) (hb : d235938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234551, d235938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234551, d235938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57310 q ha hb
  have h12 (q : Pattern) (ha : d234553 q = 1) (hb : d235940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234553, d235940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234553, d235940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57311 q ha hb
  have h13 (q : Pattern) (ha : d234554 q = 1) (hb : d235941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234554, d235941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234554, d235941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234555 q = 1) (hb : d235942 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234555, d235942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234555, d235942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d234556 q = 1) (hb : d235943 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234556, d235943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d234556, d235943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d234557 q = 1) (hb : d235944 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d234557, d235944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d234557, d235944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d234646 q = 1) (hb : d236013 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234646, d236013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234646, d236013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57324 q ha hb
  have h18 (q : Pattern) (ha : d234653 q = 1) (hb : d236024 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234653, d236024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234653, d236024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57326 q ha hb
  have h19 (q : Pattern) (ha : d234654 q = 1) (hb : d236025 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234654, d236025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d234654, d236025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d234655 q = 1) (hb : d236026 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234655, d236026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d234655, d236026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d234656 q = 1) (hb : d236027 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234656, d236027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d234656, d236027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d234657 q = 1) (hb : d236028 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d234657, d236028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d234657, d236028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d234658 q = 1) (hb : d236029 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d234658, d236029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d234658, d236029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro57328 (p : Pattern) (ha : d234664 p = 1) (hb : d236035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234659 q = 1) (hb : d236030 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d234659, d236030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234659, d236030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57327 q ha hb
  have h2 (q : Pattern) (ha : d234660 q = 1) (hb : d236031 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d234660, d236031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234660, d236031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234661 q = 1) (hb : d236032 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d234661, d236032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234661, d236032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234662 q = 1) (hb : d236033 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d234662, d236033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234662, d236033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234663 q = 1) (hb : d236034 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d234663, d236034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234663, d236034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234664 q = 1) (hb : d236035 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d234664, d236035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234664, d236035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57329 (p : Pattern) (ha : d234670 p = 1) (hb : d236041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d233601 q = 1) (hb : d235042 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d233601, d235042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57091 q ha hb
    | true =>
      simp only [d233601, d235042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57118 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d233802 q = 1) (hb : d235261 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d233802, d235261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233802, d235261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57164 q ha hb
  have h3 (q : Pattern) (ha : d233803 q = 1) (hb : d235262 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d233803, d235262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233803, d235262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234082 q = 1) (hb : d235501 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d234082, d235501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234082, d235501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57219 q ha hb
  have h5 (q : Pattern) (ha : d234083 q = 1) (hb : d235502 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d234083, d235502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234083, d235502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234084 q = 1) (hb : d235503 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d234084, d235503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234084, d235503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234374 q = 1) (hb : d235779 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d234374, d235779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234374, d235779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57275 q ha hb
  have h8 (q : Pattern) (ha : d234375 q = 1) (hb : d235780 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d234375, d235780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234375, d235780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234376 q = 1) (hb : d235781 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d234376, d235781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234376, d235781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234377 q = 1) (hb : d235782 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d234377, d235782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234377, d235782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234665 q = 1) (hb : d236036 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d234665, d236036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234665, d236036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57328 q ha hb
  have h12 (q : Pattern) (ha : d234666 q = 1) (hb : d236037 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d234666, d236037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234666, d236037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234667 q = 1) (hb : d236038 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d234667, d236038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234667, d236038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234668 q = 1) (hb : d236039 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d234668, d236039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234668, d236039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d234669 q = 1) (hb : d236040 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d234669, d236040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d234669, d236040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d234670 q = 1) (hb : d236041 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d234670, d236041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d234670, d236041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro57330 (p : Pattern) (ha : d234676 p = 1) (hb : d236047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234671 q = 1) (hb : d236042 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d234671, d236042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57329 q ha hb
    | true =>
      simp only [d234671, d236042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234672 q = 1) (hb : d236043 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d234672, d236043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234672, d236043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234673 q = 1) (hb : d236044 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d234673, d236044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234673, d236044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234674 q = 1) (hb : d236045 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d234674, d236045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234674, d236045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234675 q = 1) (hb : d236046 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d234675, d236046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234675, d236046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234676 q = 1) (hb : d236047 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d234676, d236047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234676, d236047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57331 (p : Pattern) (ha : d234682 p = 1) (hb : d236053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234677 q = 1) (hb : d236048 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d234677, d236048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57330 q ha hb
    | true =>
      simp only [d234677, d236048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234678 q = 1) (hb : d236049 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d234678, d236049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234678, d236049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234679 q = 1) (hb : d236050 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d234679, d236050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234679, d236050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234680 q = 1) (hb : d236051 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d234680, d236051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234680, d236051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234681 q = 1) (hb : d236052 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d234681, d236052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234681, d236052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234682 q = 1) (hb : d236053 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d234682, d236053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234682, d236053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57332 (p : Pattern) (ha : d234688 p = 1) (hb : d236059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234683 q = 1) (hb : d236054 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d234683, d236054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57331 q ha hb
    | true =>
      simp only [d234683, d236054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234684 q = 1) (hb : d236055 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d234684, d236055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234684, d236055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234685 q = 1) (hb : d236056 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d234685, d236056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234685, d236056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234686 q = 1) (hb : d236057 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d234686, d236057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234686, d236057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234687 q = 1) (hb : d236058 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d234687, d236058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234687, d236058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234688 q = 1) (hb : d236059 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d234688, d236059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234688, d236059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57333 (p : Pattern) (ha : d234694 p = 1) (hb : d236065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234689 q = 1) (hb : d236060 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d234689, d236060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57332 q ha hb
    | true =>
      simp only [d234689, d236060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234690 q = 1) (hb : d236061 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d234690, d236061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234690, d236061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234691 q = 1) (hb : d236062 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d234691, d236062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234691, d236062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234692 q = 1) (hb : d236063 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d234692, d236063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234692, d236063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234693 q = 1) (hb : d236064 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d234693, d236064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234693, d236064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234694 q = 1) (hb : d236065 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d234694, d236065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234694, d236065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57334 (p : Pattern) (ha : d234700 p = 1) (hb : d236071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234695 q = 1) (hb : d236066 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d234695, d236066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57333 q ha hb
    | true =>
      simp only [d234695, d236066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234696 q = 1) (hb : d236067 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d234696, d236067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234696, d236067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234697 q = 1) (hb : d236068 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d234697, d236068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234697, d236068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234698 q = 1) (hb : d236069 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d234698, d236069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234698, d236069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234699 q = 1) (hb : d236070 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d234699, d236070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234699, d236070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234700 q = 1) (hb : d236071 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d234700, d236071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234700, d236071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57335 (p : Pattern) (ha : d234706 p = 1) (hb : d236077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234701 q = 1) (hb : d236072 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d234701, d236072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57334 q ha hb
    | true =>
      simp only [d234701, d236072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234702 q = 1) (hb : d236073 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d234702, d236073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234702, d236073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234703 q = 1) (hb : d236074 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d234703, d236074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234703, d236074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234704 q = 1) (hb : d236075 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d234704, d236075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234704, d236075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234705 q = 1) (hb : d236076 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d234705, d236076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234705, d236076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234706 q = 1) (hb : d236077 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d234706, d236077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234706, d236077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57336 (p : Pattern) (ha : d234712 p = 1) (hb : d236083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234707 q = 1) (hb : d236078 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d234707, d236078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57335 q ha hb
    | true =>
      simp only [d234707, d236078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234708 q = 1) (hb : d236079 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d234708, d236079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234708, d236079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234709 q = 1) (hb : d236080 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d234709, d236080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234709, d236080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234710 q = 1) (hb : d236081 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d234710, d236081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234710, d236081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234711 q = 1) (hb : d236082 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d234711, d236082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234711, d236082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234712 q = 1) (hb : d236083 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d234712, d236083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234712, d236083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57337 (p : Pattern) (ha : d53647 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56734 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56735 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56757 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56758 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
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
theorem andIntro57338 (p : Pattern) (ha : d53655 p = 1) (hb : d231381 p = 1) : d234988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d231381 q = 1) : d234733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56740 q ha hb
    | true =>
      simp only [d204, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56726 q ha hb
  have h2 (q : Pattern) (ha : d287 q = 1) (hb : d231381 q = 1) : d234786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d234786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d234786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288 q = 1) (hb : d231381 q = 1) : d234787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d234787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288, d234787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d289 q = 1) (hb : d231381 q = 1) : d234788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d234788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d234788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290 q = 1) (hb : d231381 q = 1) : d234789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d234789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d234789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53655 q = 1) (hb : d231381 q = 1) : d234988 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d234988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d234988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57339 (p : Pattern) (ha : d53665 p = 1) (hb : d231381 p = 1) : d235029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d231381 q = 1) : d234762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d234762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56744 q ha hb
    | true =>
      simp only [d244, d234762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56731 q ha hb
  have h2 (q : Pattern) (ha : d53661 q = 1) (hb : d231381 q = 1) : d235025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d235025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d235025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53662 q = 1) (hb : d231381 q = 1) : d235026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d235026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53662, d235026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53663 q = 1) (hb : d231381 q = 1) : d235027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d235027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d235027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53664 q = 1) (hb : d231381 q = 1) : d235028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d235028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d235028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53665 q = 1) (hb : d231381 q = 1) : d235029 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d235029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d235029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57340 (p : Pattern) (ha : d53671 p = 1) (hb : d231381 p = 1) : d236094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d231381 q = 1) : d234791 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d234791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56754 q ha hb
    | true =>
      simp only [d292, d234791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56755 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d231381 q = 1) : d234792 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d234792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d234792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d231381 q = 1) : d236084 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d236084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d236084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d231381 q = 1) : d236085 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d236085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d236085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d231381 q = 1) : d234989 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d234989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d234989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57338 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d231381 q = 1) : d236086 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d236086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d236086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d231381 q = 1) : d236087 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d236087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d236087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d231381 q = 1) : d236088 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d236088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d236088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d231381 q = 1) : d236089 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d236089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d236089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d231381 q = 1) : d235030 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d235030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d235030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57339 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d231381 q = 1) : d236090 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d236090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d236090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d231381 q = 1) : d236091 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d236091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d236091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d231381 q = 1) : d236092 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d236092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d236092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d231381 q = 1) : d236093 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d236093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d236093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d231381 q = 1) : d236094 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d236094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d236094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro57341 (p : Pattern) (ha : d53677 p = 1) (hb : d231381 p = 1) : d236100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57337 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d231381 q = 1) : d236095 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d236095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d236095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57340 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d231381 q = 1) : d236096 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d236096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d236096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d231381 q = 1) : d236097 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d236097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d236097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d231381 q = 1) : d236098 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d236098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d236098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d231381 q = 1) : d236099 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d236099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d236099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d231381 q = 1) : d236100 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d236100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d236100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro57342 (p : Pattern) (ha : d53680 p = 1) (hb : d231381 p = 1) : d236103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d502 q = 1) (hb : d231381 q = 1) : d234843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d234843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56785 q ha hb
    | true =>
      simp only [d502, d234843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56786 q ha hb
  have h2 (q : Pattern) (ha : d503 q = 1) (hb : d231381 q = 1) : d234906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d234906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d234906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d504 q = 1) (hb : d231381 q = 1) : d234907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d234907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d504, d234907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d505 q = 1) (hb : d231381 q = 1) : d234908 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d234908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d234908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d506 q = 1) (hb : d231381 q = 1) : d234909 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d234909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d234909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53680 q = 1) (hb : d231381 q = 1) : d236103 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, d236103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, d236103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57343 (p : Pattern) (ha : d53691 p = 1) (hb : d231381 p = 1) : d236113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53686 q = 1) (hb : d231381 q = 1) : d234881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53686, d234881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56816 q ha hb
    | true =>
      simp only [d53686, d234881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56792 q ha hb
  have h2 (q : Pattern) (ha : d53687 q = 1) (hb : d231381 q = 1) : d236109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, d236109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53687, d236109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53688 q = 1) (hb : d231381 q = 1) : d236110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d236110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53688, d236110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53689 q = 1) (hb : d231381 q = 1) : d236111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, d236111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, d236111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53690 q = 1) (hb : d231381 q = 1) : d236112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, d236112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, d236112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53691 q = 1) (hb : d231381 q = 1) : d236113 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, d236113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, d236113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57344 (p : Pattern) (ha : d53697 p = 1) (hb : d231381 p = 1) : d236119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d231381 q = 1) : d234911 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d234911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56784 q ha hb
    | true =>
      simp only [d508, d234911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56787 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d231381 q = 1) : d234912 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d234912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d234912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d231381 q = 1) : d236101 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d236101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, d236101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d231381 q = 1) : d236102 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d236102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d236102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53681 q = 1) (hb : d231381 q = 1) : d236104 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d236104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, d236104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57342 q ha hb
  have h6 (q : Pattern) (ha : d53682 q = 1) (hb : d231381 q = 1) : d236105 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d236105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53682, d236105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53683 q = 1) (hb : d231381 q = 1) : d236106 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d236106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53683, d236106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53684 q = 1) (hb : d231381 q = 1) : d236107 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d236107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53684, d236107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53685 q = 1) (hb : d231381 q = 1) : d236108 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d236108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, d236108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53692 q = 1) (hb : d231381 q = 1) : d236114 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d236114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53692, d236114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57343 q ha hb
  have h11 (q : Pattern) (ha : d53693 q = 1) (hb : d231381 q = 1) : d236115 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d236115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53693, d236115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53694 q = 1) (hb : d231381 q = 1) : d236116 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, d236116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53694, d236116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53695 q = 1) (hb : d231381 q = 1) : d236117 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, d236117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53695, d236117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53696 q = 1) (hb : d231381 q = 1) : d236118 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d236118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53696, d236118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53697 q = 1) (hb : d231381 q = 1) : d236119 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d236119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53697, d236119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro57345 (p : Pattern) (ha : d53703 p = 1) (hb : d231381 p = 1) : d236125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d231381 q = 1) : d236120 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d236120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d236120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57344 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d231381 q = 1) : d236121 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d236121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d236121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d231381 q = 1) : d236122 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d236122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d236122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d231381 q = 1) : d236123 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d236123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d236123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d231381 q = 1) : d236124 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d236124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d236124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d231381 q = 1) : d236125 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d236125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d236125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57346 (p : Pattern) (ha : d53707 p = 1) (hb : d231381 p = 1) : d236129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d794 q = 1) (hb : d231381 q = 1) : d235070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d235070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56830 q ha hb
    | true =>
      simp only [d794, d235070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56831 q ha hb
  have h2 (q : Pattern) (ha : d795 q = 1) (hb : d231381 q = 1) : d235071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d235071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d235071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d796 q = 1) (hb : d231381 q = 1) : d235072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d235072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d796, d235072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d797 q = 1) (hb : d231381 q = 1) : d235073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d235073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d235073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d798 q = 1) (hb : d231381 q = 1) : d235074 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d235074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d235074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53707 q = 1) (hb : d231381 q = 1) : d236129 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, d236129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, d236129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57347 (p : Pattern) (ha : d53718 p = 1) (hb : d231381 p = 1) : d236140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53713 q = 1) (hb : d231381 q = 1) : d236135 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53713, d236135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56868 q ha hb
    | true =>
      simp only [d53713, d236135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56839 q ha hb
  have h2 (q : Pattern) (ha : d53714 q = 1) (hb : d231381 q = 1) : d236136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, d236136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53714, d236136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53715 q = 1) (hb : d231381 q = 1) : d236137 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d236137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53715, d236137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53716 q = 1) (hb : d231381 q = 1) : d236138 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, d236138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, d236138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53717 q = 1) (hb : d231381 q = 1) : d236139 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, d236139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, d236139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53718 q = 1) (hb : d231381 q = 1) : d236140 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, d236140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, d236140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57348 (p : Pattern) (ha : d53724 p = 1) (hb : d231381 p = 1) : d236146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d231381 q = 1) : d235076 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d235076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56829 q ha hb
    | true =>
      simp only [d800, d235076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56832 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d231381 q = 1) : d235077 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d235077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d235077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d231381 q = 1) : d236127 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d236127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, d236127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d231381 q = 1) : d236128 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d236128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d236128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53708 q = 1) (hb : d231381 q = 1) : d236130 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d236130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, d236130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57346 q ha hb
  have h6 (q : Pattern) (ha : d53709 q = 1) (hb : d231381 q = 1) : d236131 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d236131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53709, d236131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53710 q = 1) (hb : d231381 q = 1) : d236132 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d236132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53710, d236132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53711 q = 1) (hb : d231381 q = 1) : d236133 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d236133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53711, d236133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53712 q = 1) (hb : d231381 q = 1) : d236134 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d236134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, d236134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53719 q = 1) (hb : d231381 q = 1) : d236141 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d236141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53719, d236141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57347 q ha hb
  have h11 (q : Pattern) (ha : d53720 q = 1) (hb : d231381 q = 1) : d236142 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d236142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53720, d236142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53721 q = 1) (hb : d231381 q = 1) : d236143 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, d236143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53721, d236143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53722 q = 1) (hb : d231381 q = 1) : d236144 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, d236144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53722, d236144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53723 q = 1) (hb : d231381 q = 1) : d236145 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d236145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53723, d236145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53724 q = 1) (hb : d231381 q = 1) : d236146 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d236146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53724, d236146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro57349 (p : Pattern) (ha : d53730 p = 1) (hb : d231381 p = 1) : d236152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d231381 q = 1) : d236147 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d236147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d236147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57348 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d231381 q = 1) : d236148 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d236148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d236148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d231381 q = 1) : d236149 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d236149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d236149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d231381 q = 1) : d236150 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d236150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d236150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d231381 q = 1) : d236151 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d236151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d236151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d231381 q = 1) : d236152 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d236152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d236152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57350 (p : Pattern) (ha : d53735 p = 1) (hb : d231381 p = 1) : d236157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1173 q = 1) (hb : d231381 q = 1) : d235300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d235300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56888 q ha hb
    | true =>
      simp only [d1173, d235300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56889 q ha hb
  have h2 (q : Pattern) (ha : d1174 q = 1) (hb : d231381 q = 1) : d235301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d235301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d235301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1175 q = 1) (hb : d231381 q = 1) : d235302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d235302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1175, d235302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1176 q = 1) (hb : d231381 q = 1) : d235303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d235303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d235303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1177 q = 1) (hb : d231381 q = 1) : d235304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d235304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d235304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53735 q = 1) (hb : d231381 q = 1) : d236157 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d236157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d236157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57351 (p : Pattern) (ha : d53746 p = 1) (hb : d231381 p = 1) : d236168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53741 q = 1) (hb : d231381 q = 1) : d236163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53741, d236163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56926 q ha hb
    | true =>
      simp only [d53741, d236163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56897 q ha hb
  have h2 (q : Pattern) (ha : d53742 q = 1) (hb : d231381 q = 1) : d236164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, d236164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53742, d236164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53743 q = 1) (hb : d231381 q = 1) : d236165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d236165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53743, d236165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53744 q = 1) (hb : d231381 q = 1) : d236166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, d236166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, d236166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53745 q = 1) (hb : d231381 q = 1) : d236167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, d236167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, d236167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53746 q = 1) (hb : d231381 q = 1) : d236168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d236168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d236168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57352 (p : Pattern) (ha : d53752 p = 1) (hb : d231381 p = 1) : d236174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d231381 q = 1) : d235306 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d235306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56887 q ha hb
    | true =>
      simp only [d1179, d235306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56890 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d231381 q = 1) : d235307 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d235307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d235307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d231381 q = 1) : d236155 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d236155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, d236155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d231381 q = 1) : d236156 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d236156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d236156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53736 q = 1) (hb : d231381 q = 1) : d236158 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d236158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, d236158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57350 q ha hb
  have h6 (q : Pattern) (ha : d53737 q = 1) (hb : d231381 q = 1) : d236159 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d236159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53737, d236159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53738 q = 1) (hb : d231381 q = 1) : d236160 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d236160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53738, d236160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53739 q = 1) (hb : d231381 q = 1) : d236161 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d236161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53739, d236161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53740 q = 1) (hb : d231381 q = 1) : d236162 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d236162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, d236162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53747 q = 1) (hb : d231381 q = 1) : d236169 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d236169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53747, d236169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57351 q ha hb
  have h11 (q : Pattern) (ha : d53748 q = 1) (hb : d231381 q = 1) : d236170 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d236170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53748, d236170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53749 q = 1) (hb : d231381 q = 1) : d236171 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, d236171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53749, d236171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53750 q = 1) (hb : d231381 q = 1) : d236172 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, d236172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53750, d236172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53751 q = 1) (hb : d231381 q = 1) : d236173 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d236173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53751, d236173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53752 q = 1) (hb : d231381 q = 1) : d236174 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d236174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53752, d236174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro57353 (p : Pattern) (ha : d53758 p = 1) (hb : d231381 p = 1) : d236180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d231381 q = 1) : d236175 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d236175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d236175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57352 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d231381 q = 1) : d236176 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d236176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d236176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d231381 q = 1) : d236177 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d236177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d236177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d231381 q = 1) : d236178 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d236178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d236178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d231381 q = 1) : d236179 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d236179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d236179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d231381 q = 1) : d236180 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d236180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d236180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57354 (p : Pattern) (ha : d53764 p = 1) (hb : d231381 p = 1) : d236186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1634 q = 1) (hb : d231381 q = 1) : d235565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d235565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56946 q ha hb
    | true =>
      simp only [d1634, d235565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56947 q ha hb
  have h2 (q : Pattern) (ha : d1635 q = 1) (hb : d231381 q = 1) : d235566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d235566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d235566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1636 q = 1) (hb : d231381 q = 1) : d235567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d235567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1636, d235567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1637 q = 1) (hb : d231381 q = 1) : d235568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d235568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d235568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1638 q = 1) (hb : d231381 q = 1) : d235569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d235569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d235569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53764 q = 1) (hb : d231381 q = 1) : d236186 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d236186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d236186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57355 (p : Pattern) (ha : d53775 p = 1) (hb : d231381 p = 1) : d236197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53770 q = 1) (hb : d231381 q = 1) : d236192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53770, d236192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56984 q ha hb
    | true =>
      simp only [d53770, d236192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56955 q ha hb
  have h2 (q : Pattern) (ha : d53771 q = 1) (hb : d231381 q = 1) : d236193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53771, d236193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53771, d236193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53772 q = 1) (hb : d231381 q = 1) : d236194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d236194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53772, d236194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53773 q = 1) (hb : d231381 q = 1) : d236195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, d236195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, d236195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53774 q = 1) (hb : d231381 q = 1) : d236196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, d236196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, d236196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53775 q = 1) (hb : d231381 q = 1) : d236197 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, d236197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, d236197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57356 (p : Pattern) (ha : d53781 p = 1) (hb : d231381 p = 1) : d236203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d231381 q = 1) : d235571 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d235571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56945 q ha hb
    | true =>
      simp only [d1640, d235571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56948 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d231381 q = 1) : d235572 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d235572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d235572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d231381 q = 1) : d236184 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d236184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, d236184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d231381 q = 1) : d236185 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d236185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d236185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53765 q = 1) (hb : d231381 q = 1) : d236187 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d236187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, d236187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57354 q ha hb
  have h6 (q : Pattern) (ha : d53766 q = 1) (hb : d231381 q = 1) : d236188 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d236188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53766, d236188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53767 q = 1) (hb : d231381 q = 1) : d236189 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d236189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53767, d236189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53768 q = 1) (hb : d231381 q = 1) : d236190 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, d236190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53768, d236190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53769 q = 1) (hb : d231381 q = 1) : d236191 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d236191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53769, d236191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53776 q = 1) (hb : d231381 q = 1) : d236198 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d236198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53776, d236198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57355 q ha hb
  have h11 (q : Pattern) (ha : d53777 q = 1) (hb : d231381 q = 1) : d236199 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d236199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53777, d236199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53778 q = 1) (hb : d231381 q = 1) : d236200 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, d236200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53778, d236200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53779 q = 1) (hb : d231381 q = 1) : d236201 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, d236201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53779, d236201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53780 q = 1) (hb : d231381 q = 1) : d236202 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, d236202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53780, d236202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53781 q = 1) (hb : d231381 q = 1) : d236203 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d236203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53781, d236203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro57357 (p : Pattern) (ha : d53787 p = 1) (hb : d231381 p = 1) : d236209 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d231381 q = 1) : d236204 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d236204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d236204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57356 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d231381 q = 1) : d236205 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d236205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d236205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d231381 q = 1) : d236206 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d236206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d236206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d231381 q = 1) : d236207 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d236207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d236207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d231381 q = 1) : d236208 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d236208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d236208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d231381 q = 1) : d236209 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d236209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d236209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57358 (p : Pattern) (ha : d53794 p = 1) (hb : d231381 p = 1) : d236216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2117 q = 1) (hb : d231381 q = 1) : d235837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d235837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57004 q ha hb
    | true =>
      simp only [d2117, d235837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57005 q ha hb
  have h2 (q : Pattern) (ha : d2118 q = 1) (hb : d231381 q = 1) : d235838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d235838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d235838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2119 q = 1) (hb : d231381 q = 1) : d235839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d235839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2119, d235839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2120 q = 1) (hb : d231381 q = 1) : d235840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d235840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d235840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2121 q = 1) (hb : d231381 q = 1) : d235841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d235841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d235841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53794 q = 1) (hb : d231381 q = 1) : d236216 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, d236216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, d236216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57359 (p : Pattern) (ha : d53805 p = 1) (hb : d231381 p = 1) : d236227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53800 q = 1) (hb : d231381 q = 1) : d236222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53800, d236222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57042 q ha hb
    | true =>
      simp only [d53800, d236222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57013 q ha hb
  have h2 (q : Pattern) (ha : d53801 q = 1) (hb : d231381 q = 1) : d236223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53801, d236223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53801, d236223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53802 q = 1) (hb : d231381 q = 1) : d236224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d236224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53802, d236224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53803 q = 1) (hb : d231381 q = 1) : d236225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, d236225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, d236225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53804 q = 1) (hb : d231381 q = 1) : d236226 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, d236226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, d236226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53805 q = 1) (hb : d231381 q = 1) : d236227 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, d236227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, d236227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57360 (p : Pattern) (ha : d53811 p = 1) (hb : d231381 p = 1) : d236233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d231381 q = 1) : d235843 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d235843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57003 q ha hb
    | true =>
      simp only [d2123, d235843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57006 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d231381 q = 1) : d235844 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d235844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d235844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d231381 q = 1) : d236214 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d236214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, d236214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d231381 q = 1) : d236215 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d236215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d236215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53795 q = 1) (hb : d231381 q = 1) : d236217 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d236217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, d236217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57358 q ha hb
  have h6 (q : Pattern) (ha : d53796 q = 1) (hb : d231381 q = 1) : d236218 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d236218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53796, d236218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53797 q = 1) (hb : d231381 q = 1) : d236219 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d236219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53797, d236219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53798 q = 1) (hb : d231381 q = 1) : d236220 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, d236220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53798, d236220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53799 q = 1) (hb : d231381 q = 1) : d236221 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d236221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53799, d236221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53806 q = 1) (hb : d231381 q = 1) : d236228 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d236228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53806, d236228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57359 q ha hb
  have h11 (q : Pattern) (ha : d53807 q = 1) (hb : d231381 q = 1) : d236229 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d236229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53807, d236229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53808 q = 1) (hb : d231381 q = 1) : d236230 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, d236230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53808, d236230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53809 q = 1) (hb : d231381 q = 1) : d236231 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, d236231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53809, d236231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53810 q = 1) (hb : d231381 q = 1) : d236232 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, d236232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53810, d236232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53811 q = 1) (hb : d231381 q = 1) : d236233 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d236233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53811, d236233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro57361 (p : Pattern) (ha : d53817 p = 1) (hb : d231381 p = 1) : d236239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d231381 q = 1) : d236234 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d236234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d236234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57360 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d231381 q = 1) : d236235 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d236235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d236235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d231381 q = 1) : d236236 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d236236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d236236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d231381 q = 1) : d236237 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d236237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d236237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d231381 q = 1) : d236238 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d236238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d236238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d231381 q = 1) : d236239 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d236239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d236239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57362 (p : Pattern) (ha : d53823 p = 1) (hb : d231381 p = 1) : d236245 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d231381 q = 1) : d236126 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d236126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57341 q ha hb
    | true =>
      simp only [d53704, d236126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57345 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d231381 q = 1) : d236153 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d236153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d236153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57349 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d231381 q = 1) : d236154 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d236154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d236154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d231381 q = 1) : d236181 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d236181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d236181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57353 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d231381 q = 1) : d236182 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d236182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d236182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d231381 q = 1) : d236183 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d236183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d236183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d231381 q = 1) : d236210 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d236210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d236210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57357 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d231381 q = 1) : d236211 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d236211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d236211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d231381 q = 1) : d236212 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d236212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d236212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d231381 q = 1) : d236213 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d236213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d236213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d231381 q = 1) : d236240 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d236240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d236240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57361 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d231381 q = 1) : d236241 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d236241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d236241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d231381 q = 1) : d236242 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d236242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d236242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d231381 q = 1) : d236243 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d236243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d236243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d231381 q = 1) : d236244 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d236244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d236244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d231381 q = 1) : d236245 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d236245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d236245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro57363 (p : Pattern) (ha : d53829 p = 1) (hb : d231381 p = 1) : d236251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d231381 q = 1) : d236246 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d236246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57362 q ha hb
    | true =>
      simp only [d53824, d236246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d231381 q = 1) : d236247 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d236247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d236247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d231381 q = 1) : d236248 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d236248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d236248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d231381 q = 1) : d236249 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d236249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d236249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d231381 q = 1) : d236250 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d236250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d236250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d231381 q = 1) : d236251 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d236251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d236251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57364 (p : Pattern) (ha : d53835 p = 1) (hb : d231381 p = 1) : d236257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d231381 q = 1) : d236252 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d236252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57363 q ha hb
    | true =>
      simp only [d53830, d236252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d231381 q = 1) : d236253 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d236253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d236253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d231381 q = 1) : d236254 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d236254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d236254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d231381 q = 1) : d236255 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d236255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d236255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d231381 q = 1) : d236256 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d236256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d236256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d231381 q = 1) : d236257 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d236257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d236257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57365 (p : Pattern) (ha : d53841 p = 1) (hb : d231382 p = 1) : d236263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d231382 q = 1) : d236258 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d231382, d236258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57364 q ha hb
    | true =>
      simp only [d53836, d231382, d236258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231382 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53837 q = 1) (hb : d231382 q = 1) : d236259 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d236259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d236259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53838 q = 1) (hb : d231382 q = 1) : d236260 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d236260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53838, d236260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53839 q = 1) (hb : d231382 q = 1) : d236261 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d236261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53839, d236261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d53840 q = 1) (hb : d231382 q = 1) : d236262 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d236262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53840, d236262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d53841 q = 1) (hb : d231382 q = 1) : d236263 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d236263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53841, d236263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro57366 (p : Pattern) (ha : d53847 p = 1) (hb : d231382 p = 1) : d236269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231382 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d231382 q = 1) : d236264 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d236264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57365 q ha hb
    | true =>
      simp only [d53842, d236264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d231382 q = 1) : d236265 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d236265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d236265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d231382 q = 1) : d236266 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d236266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d236266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d231382 q = 1) : d236267 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d236267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d236267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d231382 q = 1) : d236268 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d236268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d236268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d231382 q = 1) : d236269 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d236269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d236269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57367 (p : Pattern) (ha : d53853 p = 1) (hb : d231382 p = 1) : d236275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231382 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d231382 q = 1) : d236270 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d236270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57366 q ha hb
    | true =>
      simp only [d53848, d236270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d231382 q = 1) : d236271 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d236271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d236271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d231382 q = 1) : d236272 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d236272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d236272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d231382 q = 1) : d236273 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d236273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d236273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d231382 q = 1) : d236274 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d236274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d236274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d231382 q = 1) : d236275 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d236275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d236275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57368 (p : Pattern) (ha : d53859 p = 1) (hb : d231382 p = 1) : d236281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231382 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d231382 q = 1) : d236276 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d236276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57367 q ha hb
    | true =>
      simp only [d53854, d236276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d231382 q = 1) : d236277 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d236277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d236277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d231382 q = 1) : d236278 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d236278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d236278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d231382 q = 1) : d236279 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d236279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d236279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d231382 q = 1) : d236280 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d236280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d236280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d231382 q = 1) : d236281 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d236281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d236281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57369 (p : Pattern) (ha : d53865 p = 1) (hb : d231382 p = 1) : d236287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231382 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d231382 q = 1) : d236282 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d236282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57368 q ha hb
    | true =>
      simp only [d53860, d236282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d231382 q = 1) : d236283 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d236283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d236283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d231382 q = 1) : d236284 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d236284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d236284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d231382 q = 1) : d236285 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d236285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d236285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d231382 q = 1) : d236286 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d236286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d236286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d231382 q = 1) : d236287 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d236287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d236287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57370 (p : Pattern) (ha : d233392 p = 1) (hb : d234783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233360 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233366 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d233387 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d233282 q = 1) (hb : d234726 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233282, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57061 q ha hb
    | true =>
      simp only [d233282, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d233388 q = 1) (hb : d234779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233388, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d233388, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d233283 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d233389 q = 1) (hb : d234780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233389, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d233389, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d233390 q = 1) (hb : d234781 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233390, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d233390, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d233391 q = 1) (hb : d234782 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233391, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233391, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d233392 q = 1) (hb : d234783 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233392, d234783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233392, d234783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57371 (p : Pattern) (ha : d233408 p = 1) (hb : d234790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d233360 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233366 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233387 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d233282 q = 1) (hb : d234726 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233282, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57061 q ha hb
    | true =>
      simp only [d233282, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d233388 q = 1) (hb : d234779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233388, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d233388, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d233283 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d233389 q = 1) (hb : d234780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233389, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d233389, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d233390 q = 1) (hb : d234781 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233390, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233390, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d233391 q = 1) (hb : d234782 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233391, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233391, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d233397 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d233401 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d233403 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d233289 q = 1) (hb : d234733 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233289, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57063 q ha hb
    | true =>
      simp only [d233289, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d233404 q = 1) (hb : d234786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233404, d234786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d233404, d234786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d233290 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d233405 q = 1) (hb : d234787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233405, d234787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d233405, d234787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d233406 q = 1) (hb : d234788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233406, d234788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d233406, d234788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d233407 q = 1) (hb : d234789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233407, d234789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d233407, d234789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d233408 q = 1) (hb : d234790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233408, d234790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d233408, d234790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro57372 (p : Pattern) (ha : d233417 p = 1) (hb : d234988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233403 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d233289 q = 1) (hb : d234733 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233289, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57063 q ha hb
    | true =>
      simp only [d233289, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d233404 q = 1) (hb : d234786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233404, d234786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233404, d234786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d233290 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d233405 q = 1) (hb : d234787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233405, d234787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d233405, d234787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d233415 q = 1) (hb : d234788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233415, d234788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233415, d234788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d233416 q = 1) (hb : d234789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233416, d234789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233416, d234789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233417 q = 1) (hb : d234988 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233417, d234988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233417, d234988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57373 (p : Pattern) (ha : d233446 p = 1) (hb : d235029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233441 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d233323 q = 1) (hb : d234762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233323, d234762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57068 q ha hb
    | true =>
      simp only [d233323, d234762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d233442 q = 1) (hb : d235025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233442, d235025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233442, d235025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d233324 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d233443 q = 1) (hb : d235026 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233443, d235026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d233443, d235026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d233444 q = 1) (hb : d235027 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233444, d235027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233444, d235027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d233445 q = 1) (hb : d235028 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233445, d235028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233445, d235028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233446 q = 1) (hb : d235029 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233446, d235029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233446, d235029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57374 (p : Pattern) (ha : d233452 p = 1) (hb : d236094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d233354 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d233409 q = 1) (hb : d234791 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233409, d234791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57370 q ha hb
    | true =>
      simp only [d233409, d234791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57371 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d233412 q = 1) (hb : d234792 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233412, d234792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233412, d234792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d233413 q = 1) (hb : d236084 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233413, d236084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d233413, d236084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d233414 q = 1) (hb : d236085 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233414, d236085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233414, d236085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d233418 q = 1) (hb : d234989 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233418, d234989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d233418, d234989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57372 q ha hb
  have h8 (q : Pattern) (ha : d233419 q = 1) (hb : d236086 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233419, d236086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d233419, d236086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d233420 q = 1) (hb : d236087 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233420, d236087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d233420, d236087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d233421 q = 1) (hb : d236088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233421, d236088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d233421, d236088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d233422 q = 1) (hb : d236089 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d233422, d236089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d233422, d236089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d233447 q = 1) (hb : d235030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233447, d235030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d233447, d235030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57373 q ha hb
  have h13 (q : Pattern) (ha : d233448 q = 1) (hb : d236090 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233448, d236090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d233448, d236090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d233449 q = 1) (hb : d236091 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233449, d236091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d233449, d236091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d233450 q = 1) (hb : d236092 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233450, d236092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d233450, d236092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d233451 q = 1) (hb : d236093 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d233451, d236093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d233451, d236093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d233452 q = 1) (hb : d236094 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d233452, d236094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d233452, d236094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro57375 (p : Pattern) (ha : d233458 p = 1) (hb : d236100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d233339 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d233453 q = 1) (hb : d236095 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d233453, d236095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233453, d236095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57374 q ha hb
  have h3 (q : Pattern) (ha : d233454 q = 1) (hb : d236096 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d233454, d236096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233454, d236096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d233455 q = 1) (hb : d236097 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d233455, d236097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233455, d236097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d233456 q = 1) (hb : d236098 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d233456, d236098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233456, d236098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233457 q = 1) (hb : d236099 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d233457, d236099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233457, d236099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d233458 q = 1) (hb : d236100 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d233458, d236100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233458, d236100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro57376 (p : Pattern) (ha : d233517 p = 1) (hb : d234903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233485 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d233506 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d233387 q = 1) (hb : d234827 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233387, d234827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57078 q ha hb
    | true =>
      simp only [d233387, d234827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57061 q ha hb
  have h5 (q : Pattern) (ha : d233507 q = 1) (hb : d234899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233507, d234899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d233507, d234899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d233513 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d233514 q = 1) (hb : d234900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233514, d234900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d233514, d234900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d233515 q = 1) (hb : d234901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233515, d234901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d233515, d234901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d233516 q = 1) (hb : d234902 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233516, d234902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233516, d234902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d233517 q = 1) (hb : d234903 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233517, d234903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233517, d234903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57377 (p : Pattern) (ha : d233536 p = 1) (hb : d234910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d233479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233485 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233506 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d233387 q = 1) (hb : d234827 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233387, d234827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57078 q ha hb
    | true =>
      simp only [d233387, d234827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57061 q ha hb
  have h4 (q : Pattern) (ha : d233507 q = 1) (hb : d234899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233507, d234899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d233507, d234899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d233513 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d233514 q = 1) (hb : d234900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233514, d234900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d233514, d234900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d233515 q = 1) (hb : d234901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233515, d234901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233515, d234901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233516 q = 1) (hb : d234902 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233516, d234902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233516, d234902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d233522 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d233526 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d233528 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d233403 q = 1) (hb : d234843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233403, d234843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57082 q ha hb
    | true =>
      simp only [d233403, d234843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57063 q ha hb
  have h13 (q : Pattern) (ha : d233529 q = 1) (hb : d234906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233529, d234906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d233529, d234906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d233532 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d233533 q = 1) (hb : d234907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233533, d234907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d233533, d234907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d233534 q = 1) (hb : d234908 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233534, d234908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d233534, d234908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d233535 q = 1) (hb : d234909 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233535, d234909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d233535, d234909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d233536 q = 1) (hb : d234910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233536, d234910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d233536, d234910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro57378 (p : Pattern) (ha : d233545 p = 1) (hb : d236103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233528 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d233403 q = 1) (hb : d234843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233403, d234843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57082 q ha hb
    | true =>
      simp only [d233403, d234843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57063 q ha hb
  have h3 (q : Pattern) (ha : d233529 q = 1) (hb : d234906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233529, d234906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233529, d234906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d233532 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d233533 q = 1) (hb : d234907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233533, d234907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d233533, d234907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d233543 q = 1) (hb : d234908 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233543, d234908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233543, d234908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d233544 q = 1) (hb : d234909 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233544, d234909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233544, d234909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233545 q = 1) (hb : d236103 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233545, d236103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233545, d236103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57379 (p : Pattern) (ha : d233582 p = 1) (hb : d236113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233571 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d233441 q = 1) (hb : d234881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233441, d234881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57088 q ha hb
    | true =>
      simp only [d233441, d234881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57068 q ha hb
  have h3 (q : Pattern) (ha : d233572 q = 1) (hb : d236109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233572, d236109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233572, d236109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d233578 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d233579 q = 1) (hb : d236110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233579, d236110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d233579, d236110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d233580 q = 1) (hb : d236111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233580, d236111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233580, d236111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d233581 q = 1) (hb : d236112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233581, d236112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233581, d236112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233582 q = 1) (hb : d236113 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233582, d236113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233582, d236113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57380 (p : Pattern) (ha : d233594 p = 1) (hb : d236119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d233473 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d233537 q = 1) (hb : d234911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233537, d234911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57376 q ha hb
    | true =>
      simp only [d233537, d234911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57377 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233539 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d233540 q = 1) (hb : d234912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233540, d234912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233540, d234912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d233541 q = 1) (hb : d236101 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233541, d236101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d233541, d236101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d233542 q = 1) (hb : d236102 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233542, d236102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233542, d236102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d233546 q = 1) (hb : d236104 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233546, d236104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d233546, d236104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57378 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d233548 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d233549 q = 1) (hb : d236105 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233549, d236105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d233549, d236105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d233550 q = 1) (hb : d236106 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233550, d236106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d233550, d236106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d233551 q = 1) (hb : d236107 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233551, d236107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d233551, d236107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d233552 q = 1) (hb : d236108 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d233552, d236108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d233552, d236108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d233583 q = 1) (hb : d236114 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233583, d236114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d233583, d236114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57379 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d233589 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d233590 q = 1) (hb : d236115 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233590, d236115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d233590, d236115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d233591 q = 1) (hb : d236116 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233591, d236116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d233591, d236116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d233592 q = 1) (hb : d236117 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233592, d236117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d233592, d236117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d233593 q = 1) (hb : d236118 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d233593, d236118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d233593, d236118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d233594 q = 1) (hb : d236119 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d233594, d236119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d233594, d236119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro57381 (p : Pattern) (ha : d233600 p = 1) (hb : d236125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d233595 q = 1) (hb : d236120 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d233595, d236120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233595, d236120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57380 q ha hb
  have h2 (q : Pattern) (ha : d233596 q = 1) (hb : d236121 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d233596, d236121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233596, d236121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233597 q = 1) (hb : d236122 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d233597, d236122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233597, d236122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d233598 q = 1) (hb : d236123 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d233598, d236123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233598, d236123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d233599 q = 1) (hb : d236124 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d233599, d236124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233599, d236124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233600 q = 1) (hb : d236125 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d233600, d236125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233600, d236125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57382 (p : Pattern) (ha : d233686 p = 1) (hb : d235065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233645 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233654 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d233675 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d233619 q = 1) (hb : d235060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233619, d235060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57121 q ha hb
    | true =>
      simp only [d233619, d235060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57122 q ha hb
  have h5 (q : Pattern) (ha : d233676 q = 1) (hb : d235061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233676, d235061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d233676, d235061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d233682 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d233683 q = 1) (hb : d235062 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233683, d235062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d233683, d235062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d233684 q = 1) (hb : d235063 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233684, d235063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d233684, d235063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d233685 q = 1) (hb : d235064 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233685, d235064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233685, d235064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d233686 q = 1) (hb : d235065 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233686, d235065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233686, d235065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57383 (p : Pattern) (ha : d233707 p = 1) (hb : d235075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d233645 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233654 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233675 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d233619 q = 1) (hb : d235060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233619, d235060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57121 q ha hb
    | true =>
      simp only [d233619, d235060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57122 q ha hb
  have h4 (q : Pattern) (ha : d233676 q = 1) (hb : d235061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233676, d235061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d233676, d235061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d233682 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d233683 q = 1) (hb : d235062 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233683, d235062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d233683, d235062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d233684 q = 1) (hb : d235063 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233684, d235063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233684, d235063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233685 q = 1) (hb : d235064 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233685, d235064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233685, d235064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d233692 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d233697 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d233699 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d233629 q = 1) (hb : d235070 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233629, d235070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57124 q ha hb
    | true =>
      simp only [d233629, d235070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57125 q ha hb
  have h13 (q : Pattern) (ha : d233700 q = 1) (hb : d235071 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233700, d235071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d233700, d235071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d233703 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d233704 q = 1) (hb : d235072 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233704, d235072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d233704, d235072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d233705 q = 1) (hb : d235073 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233705, d235073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d233705, d235073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d233706 q = 1) (hb : d235074 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233706, d235074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d233706, d235074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d233707 q = 1) (hb : d235075 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233707, d235075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d233707, d235075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro57384 (p : Pattern) (ha : d233727 p = 1) (hb : d236129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233699 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d233629 q = 1) (hb : d235070 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233629, d235070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57124 q ha hb
    | true =>
      simp only [d233629, d235070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57125 q ha hb
  have h3 (q : Pattern) (ha : d233700 q = 1) (hb : d235071 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233700, d235071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233700, d235071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d233703 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d233704 q = 1) (hb : d235072 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233704, d235072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d233704, d235072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d233725 q = 1) (hb : d235073 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233725, d235073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233725, d235073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d233726 q = 1) (hb : d235074 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233726, d235074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233726, d235074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233727 q = 1) (hb : d236129 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233727, d236129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233727, d236129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57385 (p : Pattern) (ha : d233782 p = 1) (hb : d236140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d233771 q = 1) (hb : d236135 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233771, d236135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57156 q ha hb
    | true =>
      simp only [d233771, d236135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57161 q ha hb
  have h3 (q : Pattern) (ha : d233772 q = 1) (hb : d236136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233772, d236136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233772, d236136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d233778 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d233779 q = 1) (hb : d236137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233779, d236137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d233779, d236137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d233780 q = 1) (hb : d236138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233780, d236138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233780, d236138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d233781 q = 1) (hb : d236139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233781, d236139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233781, d236139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233782 q = 1) (hb : d236140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233782, d236140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233782, d236140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57386 (p : Pattern) (ha : d233795 p = 1) (hb : d236146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d233637 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d233708 q = 1) (hb : d235076 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233708, d235076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57382 q ha hb
    | true =>
      simp only [d233708, d235076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57383 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233721 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d233722 q = 1) (hb : d235077 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233722, d235077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233722, d235077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d233723 q = 1) (hb : d236127 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233723, d236127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d233723, d236127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d233724 q = 1) (hb : d236128 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233724, d236128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233724, d236128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d233728 q = 1) (hb : d236130 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233728, d236130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d233728, d236130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57384 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d233730 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d233731 q = 1) (hb : d236131 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233731, d236131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d233731, d236131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d233732 q = 1) (hb : d236132 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233732, d236132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d233732, d236132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d233733 q = 1) (hb : d236133 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233733, d236133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d233733, d236133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d233734 q = 1) (hb : d236134 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d233734, d236134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d233734, d236134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d233783 q = 1) (hb : d236141 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233783, d236141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d233783, d236141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57385 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d233790 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d233791 q = 1) (hb : d236142 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233791, d236142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d233791, d236142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d233792 q = 1) (hb : d236143 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233792, d236143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d233792, d236143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d233793 q = 1) (hb : d236144 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233793, d236144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d233793, d236144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d233794 q = 1) (hb : d236145 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d233794, d236145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d233794, d236145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d233795 q = 1) (hb : d236146 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d233795, d236146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d233795, d236146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro57387 (p : Pattern) (ha : d233801 p = 1) (hb : d236152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d233796 q = 1) (hb : d236147 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d233796, d236147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233796, d236147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57386 q ha hb
  have h2 (q : Pattern) (ha : d233797 q = 1) (hb : d236148 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d233797, d236148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233797, d236148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233798 q = 1) (hb : d236149 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d233798, d236149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233798, d236149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d233799 q = 1) (hb : d236150 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d233799, d236150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233799, d236150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d233800 q = 1) (hb : d236151 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d233800, d236151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233800, d236151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233801 q = 1) (hb : d236152 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d233801, d236152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233801, d236152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57388 (p : Pattern) (ha : d233930 p = 1) (hb : d235295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233878 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233887 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d233908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d233852 q = 1) (hb : d235290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233852, d235290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57173 q ha hb
    | true =>
      simp only [d233852, d235290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57174 q ha hb
  have h5 (q : Pattern) (ha : d233909 q = 1) (hb : d235291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233909, d235291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d233909, d235291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d233926 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d233927 q = 1) (hb : d235292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233927, d235292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d233927, d235292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d233928 q = 1) (hb : d235293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233928, d235293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d233928, d235293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d233929 q = 1) (hb : d235294 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233929, d235294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233929, d235294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d233930 q = 1) (hb : d235295 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233930, d235295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233930, d235295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57389 (p : Pattern) (ha : d233951 p = 1) (hb : d235305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d233878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233887 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233908 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d233852 q = 1) (hb : d235290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233852, d235290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57173 q ha hb
    | true =>
      simp only [d233852, d235290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57174 q ha hb
  have h4 (q : Pattern) (ha : d233909 q = 1) (hb : d235291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233909, d235291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d233909, d235291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d233926 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d233927 q = 1) (hb : d235292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233927, d235292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d233927, d235292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d233928 q = 1) (hb : d235293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233928, d235293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233928, d235293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233929 q = 1) (hb : d235294 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233929, d235294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233929, d235294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d233936 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d233941 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d233943 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d233862 q = 1) (hb : d235300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233862, d235300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57176 q ha hb
    | true =>
      simp only [d233862, d235300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57177 q ha hb
  have h13 (q : Pattern) (ha : d233944 q = 1) (hb : d235301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233944, d235301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d233944, d235301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d233947 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d233948 q = 1) (hb : d235302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233948, d235302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d233948, d235302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d233949 q = 1) (hb : d235303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233949, d235303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d233949, d235303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d233950 q = 1) (hb : d235304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233950, d235304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d233950, d235304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d233951 q = 1) (hb : d235305 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233951, d235305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d233951, d235305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro57390 (p : Pattern) (ha : d233971 p = 1) (hb : d236157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233943 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d233862 q = 1) (hb : d235300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233862, d235300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57176 q ha hb
    | true =>
      simp only [d233862, d235300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57177 q ha hb
  have h3 (q : Pattern) (ha : d233944 q = 1) (hb : d235301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233944, d235301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233944, d235301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d233947 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d233948 q = 1) (hb : d235302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233948, d235302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d233948, d235302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d233969 q = 1) (hb : d235303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233969, d235303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233969, d235303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d233970 q = 1) (hb : d235304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233970, d235304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233970, d235304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233971 q = 1) (hb : d236157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233971, d236157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233971, d236157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57391 (p : Pattern) (ha : d234062 p = 1) (hb : d236168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234035 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d234040 q = 1) (hb : d236163 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234040, d236163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57211 q ha hb
    | true =>
      simp only [d234040, d236163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57216 q ha hb
  have h3 (q : Pattern) (ha : d234041 q = 1) (hb : d236164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234041, d236164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234041, d236164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d234058 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d234059 q = 1) (hb : d236165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234059, d236165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234059, d236165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d234060 q = 1) (hb : d236166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234060, d236166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234060, d236166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234061 q = 1) (hb : d236167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234061, d236167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234061, d236167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234062 q = 1) (hb : d236168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234062, d236168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234062, d236168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57392 (p : Pattern) (ha : d234075 p = 1) (hb : d236174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d233870 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d233952 q = 1) (hb : d235306 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233952, d235306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57388 q ha hb
    | true =>
      simp only [d233952, d235306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57389 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233965 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d233966 q = 1) (hb : d235307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233966, d235307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233966, d235307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d233967 q = 1) (hb : d236155 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233967, d236155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d233967, d236155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d233968 q = 1) (hb : d236156 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233968, d236156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d233968, d236156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d233972 q = 1) (hb : d236158 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233972, d236158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d233972, d236158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57390 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d233974 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d233975 q = 1) (hb : d236159 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233975, d236159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d233975, d236159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d233976 q = 1) (hb : d236160 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233976, d236160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d233976, d236160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d233977 q = 1) (hb : d236161 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233977, d236161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d233977, d236161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d233978 q = 1) (hb : d236162 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d233978, d236162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d233978, d236162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234063 q = 1) (hb : d236169 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234063, d236169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d234063, d236169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57391 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d234070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d234071 q = 1) (hb : d236170 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234071, d236170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234071, d236170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d234072 q = 1) (hb : d236171 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234072, d236171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d234072, d236171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d234073 q = 1) (hb : d236172 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234073, d236172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d234073, d236172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d234074 q = 1) (hb : d236173 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d234074, d236173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d234074, d236173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d234075 q = 1) (hb : d236174 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d234075, d236174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d234075, d236174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro57393 (p : Pattern) (ha : d234081 p = 1) (hb : d236180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234076 q = 1) (hb : d236175 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d234076, d236175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234076, d236175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57392 q ha hb
  have h2 (q : Pattern) (ha : d234077 q = 1) (hb : d236176 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d234077, d236176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234077, d236176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234078 q = 1) (hb : d236177 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d234078, d236177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234078, d236177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234079 q = 1) (hb : d236178 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d234079, d236178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234079, d236178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234080 q = 1) (hb : d236179 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d234080, d236179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234080, d236179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234081 q = 1) (hb : d236180 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d234081, d236180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234081, d236180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57394 (p : Pattern) (ha : d234218 p = 1) (hb : d235560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234160 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234169 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d234190 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d234134 q = 1) (hb : d235555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234134, d235555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57230 q ha hb
    | true =>
      simp only [d234134, d235555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57231 q ha hb
  have h5 (q : Pattern) (ha : d234191 q = 1) (hb : d235556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234191, d235556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d234191, d235556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d234214 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d234215 q = 1) (hb : d235557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234215, d235557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234215, d235557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d234216 q = 1) (hb : d235558 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234216, d235558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d234216, d235558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234217 q = 1) (hb : d235559 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234217, d235559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234217, d235559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234218 q = 1) (hb : d235560 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234218, d235560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234218, d235560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57395 (p : Pattern) (ha : d234239 p = 1) (hb : d235570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d234160 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234169 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234190 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234134 q = 1) (hb : d235555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234134, d235555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57230 q ha hb
    | true =>
      simp only [d234134, d235555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57231 q ha hb
  have h4 (q : Pattern) (ha : d234191 q = 1) (hb : d235556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234191, d235556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d234191, d235556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d234214 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d234215 q = 1) (hb : d235557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234215, d235557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234215, d235557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d234216 q = 1) (hb : d235558 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234216, d235558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234216, d235558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234217 q = 1) (hb : d235559 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234217, d235559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234217, d235559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d234224 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d234229 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d234231 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d234144 q = 1) (hb : d235565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234144, d235565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57233 q ha hb
    | true =>
      simp only [d234144, d235565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57234 q ha hb
  have h13 (q : Pattern) (ha : d234232 q = 1) (hb : d235566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234232, d235566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d234232, d235566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d234235 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d234236 q = 1) (hb : d235567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234236, d235567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234236, d235567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d234237 q = 1) (hb : d235568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234237, d235568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d234237, d235568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d234238 q = 1) (hb : d235569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234238, d235569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d234238, d235569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d234239 q = 1) (hb : d235570 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234239, d235570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234239, d235570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro57396 (p : Pattern) (ha : d234259 p = 1) (hb : d236186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234231 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d234144 q = 1) (hb : d235565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234144, d235565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57233 q ha hb
    | true =>
      simp only [d234144, d235565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57234 q ha hb
  have h3 (q : Pattern) (ha : d234232 q = 1) (hb : d235566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234232, d235566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234232, d235566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d234235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d234236 q = 1) (hb : d235567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234236, d235567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234236, d235567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d234257 q = 1) (hb : d235568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234257, d235568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234257, d235568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234258 q = 1) (hb : d235569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234258, d235569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234258, d235569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234259 q = 1) (hb : d236186 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234259, d236186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234259, d236186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57397 (p : Pattern) (ha : d234354 p = 1) (hb : d236197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234323 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d234328 q = 1) (hb : d236192 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234328, d236192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57267 q ha hb
    | true =>
      simp only [d234328, d236192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57272 q ha hb
  have h3 (q : Pattern) (ha : d234329 q = 1) (hb : d236193 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234329, d236193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234329, d236193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d234350 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d234351 q = 1) (hb : d236194 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234351, d236194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234351, d236194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d234352 q = 1) (hb : d236195 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234352, d236195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234352, d236195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234353 q = 1) (hb : d236196 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234353, d236196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234353, d236196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234354 q = 1) (hb : d236197 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234354, d236197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234354, d236197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57398 (p : Pattern) (ha : d234367 p = 1) (hb : d236203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d234152 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234240 q = 1) (hb : d235571 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234240, d235571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57394 q ha hb
    | true =>
      simp only [d234240, d235571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57395 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234254 q = 1) (hb : d235572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234254, d235572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234254, d235572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d234255 q = 1) (hb : d236184 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234255, d236184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234255, d236184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d234256 q = 1) (hb : d236185 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234256, d236185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234256, d236185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234260 q = 1) (hb : d236187 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234260, d236187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d234260, d236187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57396 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d234262 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d234263 q = 1) (hb : d236188 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234263, d236188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234263, d236188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d234264 q = 1) (hb : d236189 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234264, d236189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234264, d236189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d234265 q = 1) (hb : d236190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234265, d236190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d234265, d236190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d234266 q = 1) (hb : d236191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d234266, d236191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234266, d236191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234355 q = 1) (hb : d236198 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234355, d236198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d234355, d236198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57397 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d234362 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d234363 q = 1) (hb : d236199 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234363, d236199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234363, d236199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d234364 q = 1) (hb : d236200 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234364, d236200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d234364, d236200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d234365 q = 1) (hb : d236201 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234365, d236201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d234365, d236201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d234366 q = 1) (hb : d236202 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d234366, d236202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d234366, d236202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d234367 q = 1) (hb : d236203 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d234367, d236203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d234367, d236203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro57399 (p : Pattern) (ha : d234373 p = 1) (hb : d236209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234368 q = 1) (hb : d236204 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d234368, d236204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234368, d236204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57398 q ha hb
  have h2 (q : Pattern) (ha : d234369 q = 1) (hb : d236205 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d234369, d236205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234369, d236205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234370 q = 1) (hb : d236206 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d234370, d236206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234370, d236206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234371 q = 1) (hb : d236207 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d234371, d236207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234371, d236207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234372 q = 1) (hb : d236208 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d234372, d236208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234372, d236208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234373 q = 1) (hb : d236209 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d234373, d236209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234373, d236209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57400 (p : Pattern) (ha : d234509 p = 1) (hb : d235832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234462 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d234482 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d234427 q = 1) (hb : d235827 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234427, d235827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57284 q ha hb
    | true =>
      simp only [d234427, d235827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57285 q ha hb
  have h5 (q : Pattern) (ha : d234483 q = 1) (hb : d235828 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234483, d235828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d234483, d235828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d234505 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d234506 q = 1) (hb : d235829 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234506, d235829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234506, d235829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d234507 q = 1) (hb : d235830 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234507, d235830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d234507, d235830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234508 q = 1) (hb : d235831 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234508, d235831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234508, d235831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234509 q = 1) (hb : d235832 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234509, d235832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234509, d235832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57401 (p : Pattern) (ha : d234530 p = 1) (hb : d235842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d234453 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234462 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234427 q = 1) (hb : d235827 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234427, d235827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57284 q ha hb
    | true =>
      simp only [d234427, d235827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57285 q ha hb
  have h4 (q : Pattern) (ha : d234483 q = 1) (hb : d235828 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234483, d235828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d234483, d235828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d234505 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d234506 q = 1) (hb : d235829 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234506, d235829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234506, d235829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d234507 q = 1) (hb : d235830 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234507, d235830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234507, d235830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234508 q = 1) (hb : d235831 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234508, d235831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234508, d235831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d234515 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d234520 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d234522 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d234437 q = 1) (hb : d235837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234437, d235837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57287 q ha hb
    | true =>
      simp only [d234437, d235837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57288 q ha hb
  have h13 (q : Pattern) (ha : d234523 q = 1) (hb : d235838 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234523, d235838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d234523, d235838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d234526 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d234527 q = 1) (hb : d235839 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234527, d235839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234527, d235839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d234528 q = 1) (hb : d235840 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234528, d235840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d234528, d235840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d234529 q = 1) (hb : d235841 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234529, d235841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d234529, d235841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d234530 q = 1) (hb : d235842 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234530, d235842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234530, d235842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro57402 (p : Pattern) (ha : d234550 p = 1) (hb : d236216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234522 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d234437 q = 1) (hb : d235837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234437, d235837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57287 q ha hb
    | true =>
      simp only [d234437, d235837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57288 q ha hb
  have h3 (q : Pattern) (ha : d234523 q = 1) (hb : d235838 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234523, d235838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234523, d235838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d234526 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d234527 q = 1) (hb : d235839 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234527, d235839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234527, d235839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d234548 q = 1) (hb : d235840 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234548, d235840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234548, d235840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234549 q = 1) (hb : d235841 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234549, d235841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234549, d235841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234550 q = 1) (hb : d236216 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234550, d236216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234550, d236216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57403 (p : Pattern) (ha : d234645 p = 1) (hb : d236227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234614 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d234619 q = 1) (hb : d236222 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d234619, d236222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57320 q ha hb
    | true =>
      simp only [d234619, d236222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57325 q ha hb
  have h3 (q : Pattern) (ha : d234620 q = 1) (hb : d236223 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234620, d236223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234620, d236223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d234641 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d234642 q = 1) (hb : d236224 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234642, d236224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234642, d236224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d234643 q = 1) (hb : d236225 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234643, d236225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234643, d236225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234644 q = 1) (hb : d236226 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234644, d236226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234644, d236226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234645 q = 1) (hb : d236227 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234645, d236227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234645, d236227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57404 (p : Pattern) (ha : d234658 p = 1) (hb : d236233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d234445 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234531 q = 1) (hb : d235843 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234531, d235843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57400 q ha hb
    | true =>
      simp only [d234531, d235843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57401 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234544 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234545 q = 1) (hb : d235844 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234545, d235844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234545, d235844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d234546 q = 1) (hb : d236214 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234546, d236214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234546, d236214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d234547 q = 1) (hb : d236215 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234547, d236215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234547, d236215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234551 q = 1) (hb : d236217 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234551, d236217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d234551, d236217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57402 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d234553 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d234554 q = 1) (hb : d236218 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234554, d236218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d234554, d236218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d234555 q = 1) (hb : d236219 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234555, d236219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234555, d236219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d234556 q = 1) (hb : d236220 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234556, d236220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d234556, d236220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d234557 q = 1) (hb : d236221 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d234557, d236221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234557, d236221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234646 q = 1) (hb : d236228 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234646, d236228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d234646, d236228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57403 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d234653 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d234654 q = 1) (hb : d236229 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234654, d236229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234654, d236229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d234655 q = 1) (hb : d236230 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d234655, d236230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d234655, d236230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d234656 q = 1) (hb : d236231 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d234656, d236231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d234656, d236231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d234657 q = 1) (hb : d236232 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d234657, d236232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d234657, d236232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d234658 q = 1) (hb : d236233 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d234658, d236233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d234658, d236233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro57405 (p : Pattern) (ha : d234664 p = 1) (hb : d236239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234659 q = 1) (hb : d236234 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d234659, d236234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234659, d236234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57404 q ha hb
  have h2 (q : Pattern) (ha : d234660 q = 1) (hb : d236235 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d234660, d236235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234660, d236235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234661 q = 1) (hb : d236236 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d234661, d236236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234661, d236236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234662 q = 1) (hb : d236237 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d234662, d236237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234662, d236237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234663 q = 1) (hb : d236238 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d234663, d236238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234663, d236238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234664 q = 1) (hb : d236239 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d234664, d236239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d234664, d236239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57406 (p : Pattern) (ha : d234670 p = 1) (hb : d236245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d233601 q = 1) (hb : d236126 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d233601, d236126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57375 q ha hb
    | true =>
      simp only [d233601, d236126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57381 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d233802 q = 1) (hb : d236153 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d233802, d236153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d233802, d236153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57387 q ha hb
  have h3 (q : Pattern) (ha : d233803 q = 1) (hb : d236154 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d233803, d236154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233803, d236154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234082 q = 1) (hb : d236181 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d234082, d236181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234082, d236181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57393 q ha hb
  have h5 (q : Pattern) (ha : d234083 q = 1) (hb : d236182 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d234083, d236182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234083, d236182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234084 q = 1) (hb : d236183 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d234084, d236183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234084, d236183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234374 q = 1) (hb : d236210 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d234374, d236210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234374, d236210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57399 q ha hb
  have h8 (q : Pattern) (ha : d234375 q = 1) (hb : d236211 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d234375, d236211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234375, d236211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234376 q = 1) (hb : d236212 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d234376, d236212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234376, d236212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234377 q = 1) (hb : d236213 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d234377, d236213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d234377, d236213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234665 q = 1) (hb : d236240 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d234665, d236240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234665, d236240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57405 q ha hb
  have h12 (q : Pattern) (ha : d234666 q = 1) (hb : d236241 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d234666, d236241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234666, d236241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234667 q = 1) (hb : d236242 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d234667, d236242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234667, d236242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234668 q = 1) (hb : d236243 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d234668, d236243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d234668, d236243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d234669 q = 1) (hb : d236244 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d234669, d236244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d234669, d236244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d234670 q = 1) (hb : d236245 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d234670, d236245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d234670, d236245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro57407 (p : Pattern) (ha : d234676 p = 1) (hb : d236251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234671 q = 1) (hb : d236246 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d234671, d236246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57406 q ha hb
    | true =>
      simp only [d234671, d236246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234672 q = 1) (hb : d236247 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d234672, d236247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234672, d236247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234673 q = 1) (hb : d236248 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d234673, d236248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234673, d236248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234674 q = 1) (hb : d236249 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d234674, d236249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234674, d236249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234675 q = 1) (hb : d236250 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d234675, d236250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234675, d236250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234676 q = 1) (hb : d236251 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d234676, d236251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234676, d236251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57408 (p : Pattern) (ha : d234682 p = 1) (hb : d236257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234677 q = 1) (hb : d236252 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d234677, d236252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57407 q ha hb
    | true =>
      simp only [d234677, d236252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234678 q = 1) (hb : d236253 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d234678, d236253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234678, d236253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234679 q = 1) (hb : d236254 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d234679, d236254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234679, d236254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234680 q = 1) (hb : d236255 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d234680, d236255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234680, d236255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234681 q = 1) (hb : d236256 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d234681, d236256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234681, d236256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234682 q = 1) (hb : d236257 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d234682, d236257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234682, d236257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57409 (p : Pattern) (ha : d234688 p = 1) (hb : d236263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234683 q = 1) (hb : d236258 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d234683, d236258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57408 q ha hb
    | true =>
      simp only [d234683, d236258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234684 q = 1) (hb : d236259 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d234684, d236259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234684, d236259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234685 q = 1) (hb : d236260 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d234685, d236260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234685, d236260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234686 q = 1) (hb : d236261 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d234686, d236261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234686, d236261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234687 q = 1) (hb : d236262 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d234687, d236262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234687, d236262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234688 q = 1) (hb : d236263 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d234688, d236263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234688, d236263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57410 (p : Pattern) (ha : d234694 p = 1) (hb : d236269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234689 q = 1) (hb : d236264 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d234689, d236264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57409 q ha hb
    | true =>
      simp only [d234689, d236264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234690 q = 1) (hb : d236265 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d234690, d236265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234690, d236265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234691 q = 1) (hb : d236266 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d234691, d236266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234691, d236266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234692 q = 1) (hb : d236267 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d234692, d236267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234692, d236267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234693 q = 1) (hb : d236268 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d234693, d236268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234693, d236268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234694 q = 1) (hb : d236269 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d234694, d236269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234694, d236269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57411 (p : Pattern) (ha : d234700 p = 1) (hb : d236275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234695 q = 1) (hb : d236270 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d234695, d236270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57410 q ha hb
    | true =>
      simp only [d234695, d236270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234696 q = 1) (hb : d236271 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d234696, d236271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234696, d236271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234697 q = 1) (hb : d236272 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d234697, d236272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234697, d236272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234698 q = 1) (hb : d236273 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d234698, d236273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234698, d236273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234699 q = 1) (hb : d236274 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d234699, d236274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234699, d236274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234700 q = 1) (hb : d236275 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d234700, d236275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234700, d236275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57412 (p : Pattern) (ha : d234706 p = 1) (hb : d236281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234701 q = 1) (hb : d236276 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d234701, d236276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57411 q ha hb
    | true =>
      simp only [d234701, d236276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234702 q = 1) (hb : d236277 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d234702, d236277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234702, d236277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234703 q = 1) (hb : d236278 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d234703, d236278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234703, d236278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234704 q = 1) (hb : d236279 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d234704, d236279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234704, d236279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234705 q = 1) (hb : d236280 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d234705, d236280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234705, d236280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234706 q = 1) (hb : d236281 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d234706, d236281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234706, d236281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57413 (p : Pattern) (ha : d234712 p = 1) (hb : d236287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234707 q = 1) (hb : d236282 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d234707, d236282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57412 q ha hb
    | true =>
      simp only [d234707, d236282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d234708 q = 1) (hb : d236283 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d234708, d236283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234708, d236283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d234709 q = 1) (hb : d236284 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d234709, d236284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234709, d236284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d234710 q = 1) (hb : d236285 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d234710, d236285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234710, d236285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d234711 q = 1) (hb : d236286 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d234711, d236286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234711, d236286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d234712 q = 1) (hb : d236287 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d234712, d236287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234712, d236287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro57414 (p : Pattern) (ha : d234783 p = 1) (hb : d236292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231481 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231487 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d231508 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d234726 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d234779 q = 1) (hb : d236288 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234779, d236288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234779, d236288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d231404 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d234780 q = 1) (hb : d236289 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234780, d236289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234780, d236289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234781 q = 1) (hb : d236290 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234781, d236290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234781, d236290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234782 q = 1) (hb : d236291 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234782, d236291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234782, d236291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234783 q = 1) (hb : d236292 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234783, d236292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234783, d236292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57415 (p : Pattern) (ha : d234790 p = 1) (hb : d236297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231481 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231508 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d234726 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d234779 q = 1) (hb : d236288 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234779, d236288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234779, d236288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d231404 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d234780 q = 1) (hb : d236289 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234780, d236289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234780, d236289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234781 q = 1) (hb : d236290 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234781, d236290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234781, d236290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234782 q = 1) (hb : d236291 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234782, d236291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234782, d236291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d231539 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d231543 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d231545 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d234733 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d234786 q = 1) (hb : d236293 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234786, d236293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234786, d236293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d231411 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d234787 q = 1) (hb : d236294 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234787, d236294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234787, d236294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d234788 q = 1) (hb : d236295 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234788, d236295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d234788, d236295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d234789 q = 1) (hb : d236296 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234789, d236296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234789, d236296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d234790 q = 1) (hb : d236297 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234790, d236297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234790, d236297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro57416 (p : Pattern) (ha : d234988 p = 1) (hb : d236304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231545 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234733 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234786 q = 1) (hb : d236293 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234786, d236293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234786, d236293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d231411 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d234787 q = 1) (hb : d236294 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234787, d236294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234787, d236294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234788 q = 1) (hb : d236302 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234788, d236302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234788, d236302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234789 q = 1) (hb : d236303 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234789, d236303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234789, d236303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234988 q = 1) (hb : d236304 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234988, d236304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234988, d236304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57417 (p : Pattern) (ha : d235029 p = 1) (hb : d236314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231585 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234762 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d235025 q = 1) (hb : d236310 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235025, d236310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235025, d236310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d231445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d235026 q = 1) (hb : d236311 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235026, d236311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235026, d236311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d235027 q = 1) (hb : d236312 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235027, d236312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235027, d236312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235028 q = 1) (hb : d236313 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235028, d236313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235028, d236313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d235029 q = 1) (hb : d236314 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d235029, d236314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235029, d236314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57418 (p : Pattern) (ha : d236094 p = 1) (hb : d236320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231475 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234791 q = 1) (hb : d236298 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234791, d236298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57414 q ha hb
    | true =>
      simp only [d234791, d236298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57415 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231555 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234792 q = 1) (hb : d236299 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234792, d236299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234792, d236299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236084 q = 1) (hb : d236300 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236084, d236300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236084, d236300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236085 q = 1) (hb : d236301 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236085, d236301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236085, d236301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234989 q = 1) (hb : d236305 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234989, d236305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234989, d236305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57416 q ha hb
  have h8 (q : Pattern) (ha : d236086 q = 1) (hb : d236306 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236086, d236306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236086, d236306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d236087 q = 1) (hb : d236307 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236087, d236307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d236087, d236307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d236088 q = 1) (hb : d236308 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236088, d236308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d236088, d236308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d236089 q = 1) (hb : d236309 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236089, d236309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236089, d236309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d235030 q = 1) (hb : d236315 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d235030, d236315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235030, d236315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57417 q ha hb
  have h13 (q : Pattern) (ha : d236090 q = 1) (hb : d236316 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236090, d236316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d236090, d236316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d236091 q = 1) (hb : d236317 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236091, d236317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d236091, d236317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d236092 q = 1) (hb : d236318 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236092, d236318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d236092, d236318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d236093 q = 1) (hb : d236319 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236093, d236319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d236093, d236319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d236094 q = 1) (hb : d236320 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d236094, d236320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d236094, d236320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro57419 (p : Pattern) (ha : d236100 p = 1) (hb : d236326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231460 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236095 q = 1) (hb : d236321 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d236095, d236321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236095, d236321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57418 q ha hb
  have h3 (q : Pattern) (ha : d236096 q = 1) (hb : d236322 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d236096, d236322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236096, d236322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d236097 q = 1) (hb : d236323 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d236097, d236323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236097, d236323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d236098 q = 1) (hb : d236324 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d236098, d236324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236098, d236324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236099 q = 1) (hb : d236325 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d236099, d236325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236099, d236325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236100 q = 1) (hb : d236326 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d236100, d236326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236100, d236326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro57420 (p : Pattern) (ha : d234903 p = 1) (hb : d236331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231648 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d231669 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d234827 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d234899 q = 1) (hb : d236327 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234899, d236327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234899, d236327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d231697 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d234900 q = 1) (hb : d236328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234900, d236328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d234900, d236328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234901 q = 1) (hb : d236329 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234901, d236329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234901, d236329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234902 q = 1) (hb : d236330 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234902, d236330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234902, d236330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234903 q = 1) (hb : d236331 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234903, d236331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234903, d236331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57421 (p : Pattern) (ha : d234910 p = 1) (hb : d236336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231669 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d234827 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d234899 q = 1) (hb : d236327 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234899, d236327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d234899, d236327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d231697 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d234900 q = 1) (hb : d236328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234900, d236328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d234900, d236328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234901 q = 1) (hb : d236329 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234901, d236329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234901, d236329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d234902 q = 1) (hb : d236330 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234902, d236330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234902, d236330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d231706 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d231710 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d231712 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d234843 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d234906 q = 1) (hb : d236332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234906, d236332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d234906, d236332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d231718 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d234907 q = 1) (hb : d236333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234907, d236333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d234907, d236333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d234908 q = 1) (hb : d236334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234908, d236334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d234908, d236334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d234909 q = 1) (hb : d236335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234909, d236335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d234909, d236335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d234910 q = 1) (hb : d236336 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d234910, d236336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234910, d236336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro57422 (p : Pattern) (ha : d236103 p = 1) (hb : d236343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231712 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234843 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234906 q = 1) (hb : d236332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d234906, d236332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234906, d236332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d231718 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d234907 q = 1) (hb : d236333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d234907, d236333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d234907, d236333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234908 q = 1) (hb : d236341 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d234908, d236341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234908, d236341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234909 q = 1) (hb : d236342 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d234909, d236342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234909, d236342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236103 q = 1) (hb : d236343 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236103, d236343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236103, d236343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57423 (p : Pattern) (ha : d236113 p = 1) (hb : d236353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d234881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236109 q = 1) (hb : d236349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236109, d236349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236109, d236349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d231783 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236110 q = 1) (hb : d236350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236110, d236350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236110, d236350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236111 q = 1) (hb : d236351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236111, d236351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236111, d236351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236112 q = 1) (hb : d236352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236112, d236352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236112, d236352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236113 q = 1) (hb : d236353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236113, d236353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236113, d236353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57424 (p : Pattern) (ha : d236119 p = 1) (hb : d236359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231636 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d234911 q = 1) (hb : d236337 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d234911, d236337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57420 q ha hb
    | true =>
      simp only [d234911, d236337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57421 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231725 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d234912 q = 1) (hb : d236338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d234912, d236338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234912, d236338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236101 q = 1) (hb : d236339 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236101, d236339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236101, d236339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236102 q = 1) (hb : d236340 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236102, d236340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236102, d236340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236104 q = 1) (hb : d236344 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236104, d236344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236104, d236344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57422 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d231734 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d236105 q = 1) (hb : d236345 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236105, d236345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236105, d236345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d236106 q = 1) (hb : d236346 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236106, d236346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d236106, d236346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d236107 q = 1) (hb : d236347 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236107, d236347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d236107, d236347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d236108 q = 1) (hb : d236348 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236108, d236348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236108, d236348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d236114 q = 1) (hb : d236354 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236114, d236354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236114, d236354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57423 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d231794 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d236115 q = 1) (hb : d236355 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236115, d236355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d236115, d236355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d236116 q = 1) (hb : d236356 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236116, d236356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d236116, d236356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d236117 q = 1) (hb : d236357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236117, d236357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d236117, d236357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d236118 q = 1) (hb : d236358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236118, d236358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d236118, d236358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d236119 q = 1) (hb : d236359 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d236119, d236359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d236119, d236359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro57425 (p : Pattern) (ha : d236125 p = 1) (hb : d236365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236120 q = 1) (hb : d236360 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d236120, d236360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236120, d236360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57424 q ha hb
  have h2 (q : Pattern) (ha : d236121 q = 1) (hb : d236361 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d236121, d236361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236121, d236361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d236122 q = 1) (hb : d236362 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d236122, d236362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236122, d236362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d236123 q = 1) (hb : d236363 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d236123, d236363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236123, d236363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d236124 q = 1) (hb : d236364 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d236124, d236364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236124, d236364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236125 q = 1) (hb : d236365 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d236125, d236365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236125, d236365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57426 (p : Pattern) (ha : d235065 p = 1) (hb : d236371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231850 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231859 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d231880 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d235060 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d235061 q = 1) (hb : d236367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235061, d236367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235061, d236367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d231917 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d235062 q = 1) (hb : d236368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235062, d236368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d235062, d236368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d235063 q = 1) (hb : d236369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235063, d236369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d235063, d236369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d235064 q = 1) (hb : d236370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235064, d236370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235064, d236370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d235065 q = 1) (hb : d236371 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d235065, d236371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235065, d236371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57427 (p : Pattern) (ha : d235075 p = 1) (hb : d236376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231850 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231859 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231880 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d235060 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d235061 q = 1) (hb : d236367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235061, d236367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d235061, d236367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d231917 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235062 q = 1) (hb : d236368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235062, d236368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235062, d236368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235063 q = 1) (hb : d236369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235063, d236369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235063, d236369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d235064 q = 1) (hb : d236370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235064, d236370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235064, d236370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d231927 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d231932 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d231934 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d235070 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d235071 q = 1) (hb : d236372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235071, d236372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d235071, d236372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d231941 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d235072 q = 1) (hb : d236373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235072, d236373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d235072, d236373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d235073 q = 1) (hb : d236374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235073, d236374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d235073, d236374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d235074 q = 1) (hb : d236375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235074, d236375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d235074, d236375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d235075 q = 1) (hb : d236376 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d235075, d236376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d235075, d236376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro57428 (p : Pattern) (ha : d236129 p = 1) (hb : d236383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d235070 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d235071 q = 1) (hb : d236372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235071, d236372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235071, d236372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d231941 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d235072 q = 1) (hb : d236373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235072, d236373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235072, d236373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d235073 q = 1) (hb : d236381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235073, d236381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235073, d236381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235074 q = 1) (hb : d236382 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235074, d236382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235074, d236382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236129 q = 1) (hb : d236383 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236129, d236383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236129, d236383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57429 (p : Pattern) (ha : d236140 p = 1) (hb : d236393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d232004 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236135 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236136 q = 1) (hb : d236389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236136, d236389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236136, d236389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d232039 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236137 q = 1) (hb : d236390 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236137, d236390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236137, d236390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236138 q = 1) (hb : d236391 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236138, d236391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236138, d236391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236139 q = 1) (hb : d236392 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236139, d236392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236139, d236392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236140 q = 1) (hb : d236393 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236140, d236393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236140, d236393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57430 (p : Pattern) (ha : d236146 p = 1) (hb : d236399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d235076 q = 1) (hb : d236377 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d235076, d236377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57426 q ha hb
    | true =>
      simp only [d235076, d236377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57427 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231959 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d235077 q = 1) (hb : d236378 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d235077, d236378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235077, d236378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236127 q = 1) (hb : d236379 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236127, d236379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236127, d236379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236128 q = 1) (hb : d236380 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236128, d236380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236128, d236380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236130 q = 1) (hb : d236384 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236130, d236384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236130, d236384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57428 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d231968 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d236131 q = 1) (hb : d236385 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236131, d236385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236131, d236385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d236132 q = 1) (hb : d236386 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236132, d236386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d236132, d236386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d236133 q = 1) (hb : d236387 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236133, d236387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d236133, d236387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d236134 q = 1) (hb : d236388 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236134, d236388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236134, d236388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d236141 q = 1) (hb : d236394 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236141, d236394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236141, d236394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57429 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d232055 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d236142 q = 1) (hb : d236395 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236142, d236395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d236142, d236395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d236143 q = 1) (hb : d236396 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236143, d236396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d236143, d236396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d236144 q = 1) (hb : d236397 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236144, d236397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d236144, d236397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d236145 q = 1) (hb : d236398 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236145, d236398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d236145, d236398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d236146 q = 1) (hb : d236399 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d236146, d236399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d236146, d236399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro57431 (p : Pattern) (ha : d236152 p = 1) (hb : d236405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236147 q = 1) (hb : d236400 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d236147, d236400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236147, d236400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57430 q ha hb
  have h2 (q : Pattern) (ha : d236148 q = 1) (hb : d236401 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d236148, d236401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236148, d236401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d236149 q = 1) (hb : d236402 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d236149, d236402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236149, d236402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d236150 q = 1) (hb : d236403 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d236150, d236403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236150, d236403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d236151 q = 1) (hb : d236404 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d236151, d236404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236151, d236404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236152 q = 1) (hb : d236405 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d236152, d236405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236152, d236405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57432 (p : Pattern) (ha : d235295 p = 1) (hb : d236412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d232143 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d232152 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d232173 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d235290 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d235291 q = 1) (hb : d236408 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235291, d236408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235291, d236408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d232240 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d235292 q = 1) (hb : d236409 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235292, d236409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d235292, d236409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d235293 q = 1) (hb : d236410 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235293, d236410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d235293, d236410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d235294 q = 1) (hb : d236411 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235294, d236411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235294, d236411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d235295 q = 1) (hb : d236412 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d235295, d236412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235295, d236412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57433 (p : Pattern) (ha : d235305 p = 1) (hb : d236417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d232143 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d232152 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d232173 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d235290 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d235291 q = 1) (hb : d236408 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235291, d236408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d235291, d236408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d232240 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235292 q = 1) (hb : d236409 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235292, d236409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235292, d236409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235293 q = 1) (hb : d236410 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235293, d236410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235293, d236410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d235294 q = 1) (hb : d236411 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235294, d236411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235294, d236411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d232250 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d232255 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d232257 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d235300 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d235301 q = 1) (hb : d236413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235301, d236413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d235301, d236413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d232264 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d235302 q = 1) (hb : d236414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235302, d236414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d235302, d236414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d235303 q = 1) (hb : d236415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235303, d236415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d235303, d236415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d235304 q = 1) (hb : d236416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235304, d236416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d235304, d236416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d235305 q = 1) (hb : d236417 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d235305, d236417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d235305, d236417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro57434 (p : Pattern) (ha : d236157 p = 1) (hb : d236424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d232257 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d235300 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d235301 q = 1) (hb : d236413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235301, d236413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235301, d236413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d232264 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d235302 q = 1) (hb : d236414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235302, d236414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235302, d236414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d235303 q = 1) (hb : d236422 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235303, d236422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235303, d236422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235304 q = 1) (hb : d236423 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235304, d236423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235304, d236423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236157 q = 1) (hb : d236424 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236157, d236424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236157, d236424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57435 (p : Pattern) (ha : d236168 p = 1) (hb : d236434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d232352 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236163 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236164 q = 1) (hb : d236430 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236164, d236430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236164, d236430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d232413 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236165 q = 1) (hb : d236431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236165, d236431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236165, d236431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236166 q = 1) (hb : d236432 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236166, d236432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236166, d236432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236167 q = 1) (hb : d236433 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236167, d236433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236167, d236433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236168 q = 1) (hb : d236434 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236168, d236434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236168, d236434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57436 (p : Pattern) (ha : d236174 p = 1) (hb : d236440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d232135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d235306 q = 1) (hb : d236418 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d235306, d236418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57432 q ha hb
    | true =>
      simp only [d235306, d236418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57433 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d232282 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d235307 q = 1) (hb : d236419 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d235307, d236419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235307, d236419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236155 q = 1) (hb : d236420 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236155, d236420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236155, d236420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236156 q = 1) (hb : d236421 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236156, d236421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236156, d236421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236158 q = 1) (hb : d236425 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236158, d236425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236158, d236425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57434 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d232291 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d236159 q = 1) (hb : d236426 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236159, d236426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236159, d236426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d236160 q = 1) (hb : d236427 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236160, d236427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d236160, d236427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d236161 q = 1) (hb : d236428 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236161, d236428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d236161, d236428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d236162 q = 1) (hb : d236429 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236162, d236429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236162, d236429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d236169 q = 1) (hb : d236435 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236169, d236435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236169, d236435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57435 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d232429 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d236170 q = 1) (hb : d236436 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236170, d236436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d236170, d236436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d236171 q = 1) (hb : d236437 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236171, d236437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d236171, d236437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d236172 q = 1) (hb : d236438 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236172, d236438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d236172, d236438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d236173 q = 1) (hb : d236439 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236173, d236439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d236173, d236439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d236174 q = 1) (hb : d236440 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d236174, d236440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d236174, d236440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro57437 (p : Pattern) (ha : d236180 p = 1) (hb : d236446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236175 q = 1) (hb : d236441 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d236175, d236441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236175, d236441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57436 q ha hb
  have h2 (q : Pattern) (ha : d236176 q = 1) (hb : d236442 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d236176, d236442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236176, d236442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d236177 q = 1) (hb : d236443 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d236177, d236443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236177, d236443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d236178 q = 1) (hb : d236444 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d236178, d236444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236178, d236444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d236179 q = 1) (hb : d236445 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d236179, d236445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236179, d236445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236180 q = 1) (hb : d236446 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d236180, d236446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236180, d236446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57438 (p : Pattern) (ha : d235560 p = 1) (hb : d236454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d232519 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d232528 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d232549 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d235555 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d235556 q = 1) (hb : d236450 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235556, d236450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235556, d236450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d232623 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d235557 q = 1) (hb : d236451 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235557, d236451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d235557, d236451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d235558 q = 1) (hb : d236452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235558, d236452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d235558, d236452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d235559 q = 1) (hb : d236453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235559, d236453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235559, d236453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d235560 q = 1) (hb : d236454 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d235560, d236454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235560, d236454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57439 (p : Pattern) (ha : d235570 p = 1) (hb : d236459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d232519 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d232528 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d232549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d235555 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d235556 q = 1) (hb : d236450 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235556, d236450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d235556, d236450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d232623 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235557 q = 1) (hb : d236451 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235557, d236451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235557, d236451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235558 q = 1) (hb : d236452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235558, d236452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235558, d236452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d235559 q = 1) (hb : d236453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235559, d236453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235559, d236453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d232633 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d232638 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d232640 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d235565 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d235566 q = 1) (hb : d236455 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235566, d236455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d235566, d236455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d232647 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d235567 q = 1) (hb : d236456 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235567, d236456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d235567, d236456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d235568 q = 1) (hb : d236457 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235568, d236457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d235568, d236457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d235569 q = 1) (hb : d236458 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235569, d236458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d235569, d236458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d235570 q = 1) (hb : d236459 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d235570, d236459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d235570, d236459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro57440 (p : Pattern) (ha : d236186 p = 1) (hb : d236466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d232640 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d235565 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d235566 q = 1) (hb : d236455 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235566, d236455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235566, d236455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d232647 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d235567 q = 1) (hb : d236456 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235567, d236456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235567, d236456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d235568 q = 1) (hb : d236464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235568, d236464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235568, d236464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235569 q = 1) (hb : d236465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235569, d236465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235569, d236465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236186 q = 1) (hb : d236466 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236186, d236466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236186, d236466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57441 (p : Pattern) (ha : d236197 p = 1) (hb : d236476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d232735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236192 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236193 q = 1) (hb : d236472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236193, d236472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236193, d236472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d232800 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236194 q = 1) (hb : d236473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236194, d236473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236194, d236473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236195 q = 1) (hb : d236474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236195, d236474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236195, d236474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236196 q = 1) (hb : d236475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236196, d236475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236196, d236475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236197 q = 1) (hb : d236476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236197, d236476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236197, d236476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57442 (p : Pattern) (ha : d236203 p = 1) (hb : d236482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d232511 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d235571 q = 1) (hb : d236460 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d235571, d236460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57438 q ha hb
    | true =>
      simp only [d235571, d236460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57439 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d232665 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d235572 q = 1) (hb : d236461 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d235572, d236461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235572, d236461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236184 q = 1) (hb : d236462 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236184, d236462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236184, d236462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236185 q = 1) (hb : d236463 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236185, d236463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236185, d236463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236187 q = 1) (hb : d236467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236187, d236467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236187, d236467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57440 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d232674 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d236188 q = 1) (hb : d236468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236188, d236468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236188, d236468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d236189 q = 1) (hb : d236469 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236189, d236469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d236189, d236469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d236190 q = 1) (hb : d236470 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236190, d236470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d236190, d236470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d236191 q = 1) (hb : d236471 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236191, d236471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236191, d236471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d236198 q = 1) (hb : d236477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236198, d236477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236198, d236477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57441 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d232816 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d236199 q = 1) (hb : d236478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236199, d236478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d236199, d236478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d236200 q = 1) (hb : d236479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236200, d236479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d236200, d236479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d236201 q = 1) (hb : d236480 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236201, d236480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d236201, d236480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d236202 q = 1) (hb : d236481 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236202, d236481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d236202, d236481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d236203 q = 1) (hb : d236482 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d236203, d236482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d236203, d236482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro57443 (p : Pattern) (ha : d236209 p = 1) (hb : d236488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236204 q = 1) (hb : d236483 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d236204, d236483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236204, d236483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57442 q ha hb
  have h2 (q : Pattern) (ha : d236205 q = 1) (hb : d236484 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d236205, d236484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236205, d236484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d236206 q = 1) (hb : d236485 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d236206, d236485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236206, d236485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d236207 q = 1) (hb : d236486 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d236207, d236486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236207, d236486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d236208 q = 1) (hb : d236487 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d236208, d236487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236208, d236487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236209 q = 1) (hb : d236488 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d236209, d236488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236209, d236488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57444 (p : Pattern) (ha : d235832 p = 1) (hb : d236497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d232907 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d232916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d232936 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d235827 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d235828 q = 1) (hb : d236493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235828, d236493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235828, d236493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d233009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d235829 q = 1) (hb : d236494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235829, d236494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d235829, d236494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d235830 q = 1) (hb : d236495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235830, d236495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d235830, d236495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d235831 q = 1) (hb : d236496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235831, d236496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235831, d236496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d235832 q = 1) (hb : d236497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d235832, d236497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235832, d236497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57445 (p : Pattern) (ha : d235842 p = 1) (hb : d236502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d232907 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d232916 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d232936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d235827 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d235828 q = 1) (hb : d236493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235828, d236493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d235828, d236493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d233009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235829 q = 1) (hb : d236494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235829, d236494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235829, d236494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235830 q = 1) (hb : d236495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235830, d236495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235830, d236495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d235831 q = 1) (hb : d236496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235831, d236496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235831, d236496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d233019 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d233024 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d233026 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d235837 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d235838 q = 1) (hb : d236498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235838, d236498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d235838, d236498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d233033 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d235839 q = 1) (hb : d236499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235839, d236499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d235839, d236499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d235840 q = 1) (hb : d236500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235840, d236500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d235840, d236500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d235841 q = 1) (hb : d236501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235841, d236501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d235841, d236501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d235842 q = 1) (hb : d236502 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d235842, d236502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d235842, d236502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro57446 (p : Pattern) (ha : d236216 p = 1) (hb : d236509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233026 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d235837 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d235838 q = 1) (hb : d236498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d235838, d236498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235838, d236498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d233033 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d235839 q = 1) (hb : d236499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d235839, d236499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235839, d236499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d235840 q = 1) (hb : d236507 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d235840, d236507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235840, d236507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235841 q = 1) (hb : d236508 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d235841, d236508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d235841, d236508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236216 q = 1) (hb : d236509 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236216, d236509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236216, d236509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57447 (p : Pattern) (ha : d236227 p = 1) (hb : d236519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236222 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236223 q = 1) (hb : d236515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236223, d236515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236223, d236515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d233186 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236224 q = 1) (hb : d236516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236224, d236516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236224, d236516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236225 q = 1) (hb : d236517 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236225, d236517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236225, d236517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236226 q = 1) (hb : d236518 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236226, d236518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236226, d236518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236227 q = 1) (hb : d236519 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236227, d236519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236227, d236519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57448 (p : Pattern) (ha : d236233 p = 1) (hb : d236525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d232899 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d235843 q = 1) (hb : d236503 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d235843, d236503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57444 q ha hb
    | true =>
      simp only [d235843, d236503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57445 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d233051 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d235844 q = 1) (hb : d236504 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d235844, d236504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d235844, d236504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236214 q = 1) (hb : d236505 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236214, d236505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236214, d236505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236215 q = 1) (hb : d236506 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236215, d236506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236215, d236506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236217 q = 1) (hb : d236510 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236217, d236510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236217, d236510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57446 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d233060 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d236218 q = 1) (hb : d236511 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236218, d236511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236218, d236511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d236219 q = 1) (hb : d236512 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236219, d236512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d236219, d236512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d236220 q = 1) (hb : d236513 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236220, d236513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d236220, d236513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d236221 q = 1) (hb : d236514 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236221, d236514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236221, d236514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d236228 q = 1) (hb : d236520 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236228, d236520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236228, d236520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57447 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d233202 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d236229 q = 1) (hb : d236521 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236229, d236521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d236229, d236521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d236230 q = 1) (hb : d236522 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236230, d236522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d236230, d236522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d236231 q = 1) (hb : d236523 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236231, d236523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d236231, d236523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d236232 q = 1) (hb : d236524 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236232, d236524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d236232, d236524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d236233 q = 1) (hb : d236525 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d236233, d236525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d236233, d236525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro57449 (p : Pattern) (ha : d236239 p = 1) (hb : d236531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236234 q = 1) (hb : d236526 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d236234, d236526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236234, d236526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57448 q ha hb
  have h2 (q : Pattern) (ha : d236235 q = 1) (hb : d236527 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d236235, d236527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236235, d236527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d236236 q = 1) (hb : d236528 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d236236, d236528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236236, d236528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d236237 q = 1) (hb : d236529 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d236237, d236529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236237, d236529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d236238 q = 1) (hb : d236530 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d236238, d236530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236238, d236530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236239 q = 1) (hb : d236531 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d236239, d236531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236239, d236531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57450 (p : Pattern) (ha : d236245 p = 1) (hb : d236537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d236126 q = 1) (hb : d236366 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236126, d236366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57419 q ha hb
    | true =>
      simp only [d236126, d236366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57425 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236153 q = 1) (hb : d236406 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236153, d236406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236153, d236406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57431 q ha hb
  have h3 (q : Pattern) (ha : d236154 q = 1) (hb : d236407 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d236154, d236407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236154, d236407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d236181 q = 1) (hb : d236447 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236181, d236447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236181, d236447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57437 q ha hb
  have h5 (q : Pattern) (ha : d236182 q = 1) (hb : d236448 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d236182, d236448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236182, d236448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236183 q = 1) (hb : d236449 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d236183, d236449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236183, d236449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236210 q = 1) (hb : d236489 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236210, d236489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236210, d236489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57443 q ha hb
  have h8 (q : Pattern) (ha : d236211 q = 1) (hb : d236490 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d236211, d236490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236211, d236490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d236212 q = 1) (hb : d236491 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d236212, d236491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236212, d236491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d236213 q = 1) (hb : d236492 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d236213, d236492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236213, d236492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d236240 q = 1) (hb : d236532 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236240, d236532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236240, d236532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57449 q ha hb
  have h12 (q : Pattern) (ha : d236241 q = 1) (hb : d236533 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d236241, d236533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236241, d236533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d236242 q = 1) (hb : d236534 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d236242, d236534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236242, d236534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d236243 q = 1) (hb : d236535 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d236243, d236535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236243, d236535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d236244 q = 1) (hb : d236536 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d236244, d236536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d236244, d236536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d236245 q = 1) (hb : d236537 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d236245, d236537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d236245, d236537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro57451 (p : Pattern) (ha : d236251 p = 1) (hb : d236543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236246 q = 1) (hb : d236538 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d236246, d236538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57450 q ha hb
    | true =>
      simp only [d236246, d236538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d236247 q = 1) (hb : d236539 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d236247, d236539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236247, d236539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d236248 q = 1) (hb : d236540 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d236248, d236540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d236248, d236540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d236249 q = 1) (hb : d236541 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d236249, d236541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236249, d236541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d236250 q = 1) (hb : d236542 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d236250, d236542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236250, d236542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d236251 q = 1) (hb : d236543 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d236251, d236543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d236251, d236543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57452 (p : Pattern) (ha : d236257 p = 1) (hb : d236549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236252 q = 1) (hb : d236544 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d236252, d236544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57451 q ha hb
    | true =>
      simp only [d236252, d236544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d236253 q = 1) (hb : d236545 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d236253, d236545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236253, d236545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d236254 q = 1) (hb : d236546 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d236254, d236546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d236254, d236546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d236255 q = 1) (hb : d236547 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d236255, d236547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236255, d236547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d236256 q = 1) (hb : d236548 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d236256, d236548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236256, d236548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d236257 q = 1) (hb : d236549 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d236257, d236549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d236257, d236549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57453 (p : Pattern) (ha : d236263 p = 1) (hb : d236555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236258 q = 1) (hb : d236550 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d236258, d236550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57452 q ha hb
    | true =>
      simp only [d236258, d236550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d236259 q = 1) (hb : d236551 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d236259, d236551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236259, d236551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d236260 q = 1) (hb : d236552 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d236260, d236552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d236260, d236552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d236261 q = 1) (hb : d236553 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d236261, d236553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236261, d236553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d236262 q = 1) (hb : d236554 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d236262, d236554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236262, d236554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d236263 q = 1) (hb : d236555 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d236263, d236555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d236263, d236555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57454 (p : Pattern) (ha : d236269 p = 1) (hb : d236561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236264 q = 1) (hb : d236556 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d236264, d236556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57453 q ha hb
    | true =>
      simp only [d236264, d236556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d236265 q = 1) (hb : d236557 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d236265, d236557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236265, d236557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d236266 q = 1) (hb : d236558 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d236266, d236558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d236266, d236558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d236267 q = 1) (hb : d236559 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d236267, d236559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236267, d236559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d236268 q = 1) (hb : d236560 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d236268, d236560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236268, d236560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d236269 q = 1) (hb : d236561 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d236269, d236561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d236269, d236561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57455 (p : Pattern) (ha : d236275 p = 1) (hb : d236567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236270 q = 1) (hb : d236562 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d236270, d236562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57454 q ha hb
    | true =>
      simp only [d236270, d236562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d236271 q = 1) (hb : d236563 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d236271, d236563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236271, d236563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d236272 q = 1) (hb : d236564 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d236272, d236564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d236272, d236564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d236273 q = 1) (hb : d236565 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d236273, d236565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236273, d236565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d236274 q = 1) (hb : d236566 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d236274, d236566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236274, d236566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d236275 q = 1) (hb : d236567 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d236275, d236567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d236275, d236567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57456 (p : Pattern) (ha : d236281 p = 1) (hb : d236573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236276 q = 1) (hb : d236568 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d236276, d236568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57455 q ha hb
    | true =>
      simp only [d236276, d236568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d236277 q = 1) (hb : d236569 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d236277, d236569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236277, d236569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d236278 q = 1) (hb : d236570 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d236278, d236570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d236278, d236570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d236279 q = 1) (hb : d236571 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d236279, d236571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236279, d236571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d236280 q = 1) (hb : d236572 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d236280, d236572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236280, d236572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d236281 q = 1) (hb : d236573 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d236281, d236573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d236281, d236573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57457 (p : Pattern) (ha : d236287 p = 1) (hb : d236579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236282 q = 1) (hb : d236574 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d236282, d236574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57456 q ha hb
    | true =>
      simp only [d236282, d236574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d236283 q = 1) (hb : d236575 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d236283, d236575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236283, d236575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d236284 q = 1) (hb : d236576 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d236284, d236576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d236284, d236576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d236285 q = 1) (hb : d236577 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d236285, d236577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236285, d236577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d236286 q = 1) (hb : d236578 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d236286, d236578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236286, d236578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d236287 q = 1) (hb : d236579 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d236287, d236579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d236287, d236579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57458 (p : Pattern) (ha : d138 p = 1) (hb : d236582 p = 1) : d9381 p = 1 := by
  have h0 (q : Pattern) (ha : d135 q = 1) (hb : d236581 q = 1) : d135 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d136 q = 1) (hb : d236582 q = 1) : d5448 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d236582, d5448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d136, d236582, d5448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d137 q = 1) (hb : d236582 q = 1) : d5449 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d5449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137, d5449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23 q = 1) (hb : d236582 q = 1) : d23 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d138 q = 1) (hb : d236582 q = 1) : d9381 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d9381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138, d9381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57459 (p : Pattern) (ha : d144 p = 1) (hb : d236582 p = 1) : d16081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d236582 q = 1) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57458 q ha hb
    | true =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d236582 q = 1) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d236582 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d236582 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d236582 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d143 q = 1) (hb : d236582 q = 1) : d12495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d236582 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d144 q = 1) (hb : d236582 q = 1) : d16081 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144, d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57460 (p : Pattern) (ha : d150 p = 1) (hb : d236582 p = 1) : d23140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d236582 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d236582 q = 1) : d23135 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57459 q ha hb
    | true =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d236582 q = 1) : d23136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d236582 q = 1) : d23137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d236582 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d236582 q = 1) : d23138 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d23138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d23138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d236582 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d236582 q = 1) : d23139 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d23139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d23139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d236582 q = 1) : d23140 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d23140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d23140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro57461 (p : Pattern) (ha : d203 p = 1) (hb : d236582 p = 1) : d23153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d236582 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57460 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d236582 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d236582 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d236582 q = 1) : d23143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d236582 q = 1) : d23144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d236582 q = 1) : d23145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d23145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d23145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d236582 q = 1) : d23153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d23153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d23153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro57462 (p : Pattern) (ha : d4349 p = 1) (hb : d236582 p = 1) : d211098 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d236582 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d236582 q = 1) : d23154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57461 q ha hb
    | true =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d236582 q = 1) : d211087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d211087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d211087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d236582 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d236582 q = 1) : d211088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d211088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d211088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d236582 q = 1) : d211096 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d211096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d211096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d236582 q = 1) : d211097 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d211097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d211097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d236582 q = 1) : d211098 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d211098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d211098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57463 (p : Pattern) (ha : d231 p = 1) (hb : d236582 p = 1) : d16166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d236582 q = 1) : d12599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d12599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d12599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57458 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d236582 q = 1) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57458 q ha hb
    | true =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d236582 q = 1) : d12600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d12600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d12600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d236582 q = 1) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d236582 q = 1) : d12601 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d12601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d12601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d236582 q = 1) : d12602 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d12602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d12602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d236582 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d230 q = 1) (hb : d236582 q = 1) : d12603 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d12603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d12603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d236582 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d231 q = 1) (hb : d236582 q = 1) : d16166 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d16166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d231, d16166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57464 (p : Pattern) (ha : d237 p = 1) (hb : d236582 p = 1) : d23177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d236582 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d236582 q = 1) : d23172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57463 q ha hb
    | true =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d236582 q = 1) : d23173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d236582 q = 1) : d23174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d236582 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d236582 q = 1) : d23175 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d23175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d23175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d236582 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d236582 q = 1) : d23176 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d23176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d23176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d236582 q = 1) : d23177 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d23177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d23177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro57465 (p : Pattern) (ha : d243 p = 1) (hb : d236582 p = 1) : d23183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d236582 q = 1) : d23178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57464 q ha hb
    | true =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d236582 q = 1) : d23179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d236582 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d236582 q = 1) : d23180 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d23180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d23180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d236582 q = 1) : d23181 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d23181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d23181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d236582 q = 1) : d23182 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d23182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d23182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d236582 q = 1) : d23183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d23183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d23183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro57466 (p : Pattern) (ha : d4359 p = 1) (hb : d236582 p = 1) : d211108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d236582 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d236582 q = 1) : d23184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d23184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57465 q ha hb
    | true =>
      simp only [d244, d23184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d236582 q = 1) : d211104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d211104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d211104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d236582 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d236582 q = 1) : d211105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d211105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d211105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d236582 q = 1) : d211106 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d211106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d211106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d236582 q = 1) : d211107 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d211107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d211107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d236582 q = 1) : d211108 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d211108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d211108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57467 (p : Pattern) (ha : d156 p = 1) (hb : d236582 p = 1) : d23146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d236582 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57460 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d236582 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d236582 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d236582 q = 1) : d23143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d236582 q = 1) : d23144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d236582 q = 1) : d23145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d23145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d23145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d236582 q = 1) : d23146 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d23146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d23146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro57468 (p : Pattern) (ha : d51643 p = 1) (hb : d236582 p = 1) : d211086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d236582 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d236582 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d236582 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d236582 q = 1) : d23147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57467 q ha hb
    | true =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d236582 q = 1) : d211082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d211082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d211082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d236582 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d236582 q = 1) : d211083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d211083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d211083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d236582 q = 1) : d211084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d211084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d211084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d236582 q = 1) : d211085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d211085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d211085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d236582 q = 1) : d211086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d211086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d211086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro57469 (p : Pattern) (ha : d51646 p = 1) (hb : d236582 p = 1) : d211091 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d236582 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d236582 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d236582 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d236582 q = 1) : d23147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57467 q ha hb
    | true =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d236582 q = 1) : d211082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d211082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d211082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d236582 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d236582 q = 1) : d211083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d211083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d211083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d236582 q = 1) : d211084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d211084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d211084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d236582 q = 1) : d211085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d211085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d211085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d236582 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d236582 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d236582 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d236582 q = 1) : d23154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57461 q ha hb
    | true =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d236582 q = 1) : d211087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d211087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d211087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d236582 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d236582 q = 1) : d211088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d211088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d211088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d236582 q = 1) : d211089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d211089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d211089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d236582 q = 1) : d211090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d211090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d211090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d236582 q = 1) : d211091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d211091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d211091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro57470 (p : Pattern) (ha : d51652 p = 1) (hb : d236582 p = 1) : d211114 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d236582 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d236582 q = 1) : d211092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d211092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57468 q ha hb
    | true =>
      simp only [d51647, d211092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57469 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d236582 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d236582 q = 1) : d211093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d211093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d211093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d236582 q = 1) : d211094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d211094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d211094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d236582 q = 1) : d211095 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d211095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d211095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d236582 q = 1) : d211099 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d211099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d211099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57462 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d236582 q = 1) : d211100 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d211100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d211100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d236582 q = 1) : d211101 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d211101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d211101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d236582 q = 1) : d211102 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d211102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d211102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d236582 q = 1) : d211103 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d211103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d211103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d236582 q = 1) : d211109 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d211109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d211109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57466 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d236582 q = 1) : d211110 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d211110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d211110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d236582 q = 1) : d211111 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d211111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d211111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d236582 q = 1) : d211112 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d211112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d211112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d236582 q = 1) : d211113 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d211113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d211113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d236582 q = 1) : d211114 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d211114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d211114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro57471 (p : Pattern) (ha : d284 p = 1) (hb : d236582 p = 1) : d23205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d236582 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d236582 q = 1) : d23147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57467 q ha hb
    | true =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d236582 q = 1) : d23201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d236582 q = 1) : d23202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d23202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d23202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d236582 q = 1) : d23203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d23203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d23203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d236582 q = 1) : d23204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d23204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d23204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d236582 q = 1) : d23205 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d23205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d23205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro57472 (p : Pattern) (ha : d291 p = 1) (hb : d236582 p = 1) : d23212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d236582 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d236582 q = 1) : d23147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57467 q ha hb
    | true =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d236582 q = 1) : d23201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d236582 q = 1) : d23202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d23202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d23202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d236582 q = 1) : d23203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d23203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d23203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d236582 q = 1) : d23204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d23204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d23204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d236582 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d236582 q = 1) : d23154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57461 q ha hb
    | true =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d236582 q = 1) : d23208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d23208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d23208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d236582 q = 1) : d23209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d23209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d23209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d236582 q = 1) : d23210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d23210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d23210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d236582 q = 1) : d23211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d23211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d23211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d236582 q = 1) : d23212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d23212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d23212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro57473 (p : Pattern) (ha : d397 p = 1) (hb : d236582 p = 1) : d23297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d236582 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d236582 q = 1) : d23147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57467 q ha hb
    | true =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d236582 q = 1) : d23201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d236582 q = 1) : d23202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d23202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d23202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d236582 q = 1) : d23203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d23203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d23203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d236582 q = 1) : d23204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d23204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d23204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d236582 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d236582 q = 1) : d23297 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d23297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d23297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57474 (p : Pattern) (ha : d296 p = 1) (hb : d236582 p = 1) : d23217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d236582 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57460 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d236582 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d236582 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d236582 q = 1) : d23143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d236582 q = 1) : d23144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d236582 q = 1) : d23216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d23216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d23216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d236582 q = 1) : d23217 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d23217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d23217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro57475 (p : Pattern) (ha : d303 p = 1) (hb : d236582 p = 1) : d23224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d236582 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57460 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d236582 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d236582 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d236582 q = 1) : d23143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d236582 q = 1) : d23222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d23222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d23222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d236582 q = 1) : d23223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d23223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d23223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d236582 q = 1) : d23224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d23224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d23224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro57476 (p : Pattern) (ha : d318 p = 1) (hb : d236582 p = 1) : d23230 p = 1 := by
  have h0 (q : Pattern) (ha : d315 q = 1) (hb : d236581 q = 1) : d315 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d316 q = 1) (hb : d236582 q = 1) : d23228 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d236582, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d316, d236582, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d317 q = 1) (hb : d236582 q = 1) : d23229 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d317, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d236581 q = 1) : d135 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d136 q = 1) (hb : d236582 q = 1) : d5448 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d236582, d5448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136, d236582, d5448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d137 q = 1) (hb : d236582 q = 1) : d5449 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d5449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137, d5449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d318 q = 1) (hb : d236582 q = 1) : d23230 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d318, d23230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318, d23230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro57477 (p : Pattern) (ha : d324 p = 1) (hb : d236582 p = 1) : d23236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d236582 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57476 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d236582 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d236582 q = 1) : d23233 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d236582 q = 1) : d23234 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d236582 q = 1) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57458 q ha hb
    | true =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d236582 q = 1) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d236582 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d236582 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d236582 q = 1) : d23235 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d23235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d23235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28 q = 1) (hb : d236582 q = 1) : d28 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d143 q = 1) (hb : d236582 q = 1) : d12495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d143, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d324 q = 1) (hb : d236582 q = 1) : d23236 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d324, d23236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324, d23236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro57478 (p : Pattern) (ha : d330 p = 1) (hb : d236582 p = 1) : d23242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d236582 q = 1) : d23237 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57477 q ha hb
    | true =>
      simp only [d325, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57459 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d236582 q = 1) : d23238 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d236582 q = 1) : d23239 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d236582 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d236582 q = 1) : d23135 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57459 q ha hb
    | true =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d236582 q = 1) : d23136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d236582 q = 1) : d23137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d328 q = 1) (hb : d236582 q = 1) : d23240 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d328, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d236582 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d236582 q = 1) : d23138 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d23138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d23138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d329 q = 1) (hb : d236582 q = 1) : d23241 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d329, d23241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d329, d23241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d330 q = 1) (hb : d236582 q = 1) : d23242 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d330, d23242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d330, d23242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro57479 (p : Pattern) (ha : d336 p = 1) (hb : d236582 p = 1) : d23248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331 q = 1) (hb : d236582 q = 1) : d23243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d23243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57478 q ha hb
    | true =>
      simp only [d331, d23243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d332 q = 1) (hb : d236582 q = 1) : d23244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d23244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d332, d23244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d236582 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57460 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d236582 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d333 q = 1) (hb : d236582 q = 1) : d23245 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d23245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333, d23245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d334 q = 1) (hb : d236582 q = 1) : d23246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d23246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d334, d23246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d335 q = 1) (hb : d236582 q = 1) : d23247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d23247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d335, d23247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d336 q = 1) (hb : d236582 q = 1) : d23248 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336, d23248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d336, d23248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57480 (p : Pattern) (ha : d4736 p = 1) (hb : d236582 p = 1) : d23268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d236582 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57460 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d236582 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d236582 q = 1) : d23265 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d23265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d23265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d236582 q = 1) : d23266 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d23266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d23266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d236582 q = 1) : d23267 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d23267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d23267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d236582 q = 1) : d23268 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d23268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d23268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57481 (p : Pattern) (ha : d74579 p = 1) (hb : d236582 p = 1) : d211124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d236582 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d236582 q = 1) : d23218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d23218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57474 q ha hb
    | true =>
      simp only [d297, d23218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d236582 q = 1) : d23219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d23219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d23219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d236582 q = 1) : d23220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d23220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d23220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d236582 q = 1) : d23221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d23221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d23221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d236582 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d236582 q = 1) : d23225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d23225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57475 q ha hb
    | true =>
      simp only [d304, d23225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d236582 q = 1) : d23226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d23226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d23226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d236582 q = 1) : d23227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d23227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d23227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d337 q = 1) (hb : d236582 q = 1) : d23249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d23249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57479 q ha hb
    | true =>
      simp only [d337, d23249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57467 q ha hb
  have h11 (q : Pattern) (ha : d4371 q = 1) (hb : d236582 q = 1) : d211120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4371, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d236582 q = 1) : d23269 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d23269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57480 q ha hb
    | true =>
      simp only [d4737, d23269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d236582 q = 1) : d23270 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d23270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d23270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d74576 q = 1) (hb : d236582 q = 1) : d211121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74576, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74576, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74577 q = 1) (hb : d236582 q = 1) : d211122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74577, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74577, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74578 q = 1) (hb : d236582 q = 1) : d211123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74578, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74578, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74579 q = 1) (hb : d236582 q = 1) : d211124 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74579, d211124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74579, d211124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro57482 (p : Pattern) (ha : d376 p = 1) (hb : d236582 p = 1) : d23275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d236582 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57460 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d236582 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d236582 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d236582 q = 1) : d23143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d236582 q = 1) : d23144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d236582 q = 1) : d23216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d23216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d23216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d236582 q = 1) : d23275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d23275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d23275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro57483 (p : Pattern) (ha : d381 p = 1) (hb : d236582 p = 1) : d23280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d236582 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57460 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d236582 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d236582 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d236582 q = 1) : d23143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d236582 q = 1) : d23222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d23222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d23222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d236582 q = 1) : d23223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d23223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d23223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d236582 q = 1) : d23280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d23280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d23280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro57484 (p : Pattern) (ha : d385 p = 1) (hb : d236582 p = 1) : d23284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331 q = 1) (hb : d236582 q = 1) : d23243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d23243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57478 q ha hb
    | true =>
      simp only [d331, d23243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d332 q = 1) (hb : d236582 q = 1) : d23244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d23244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d332, d23244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d236582 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57460 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d236582 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d333 q = 1) (hb : d236582 q = 1) : d23245 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d23245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333, d23245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d334 q = 1) (hb : d236582 q = 1) : d23246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d23246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d334, d23246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d335 q = 1) (hb : d236582 q = 1) : d23247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d23247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d335, d23247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d385 q = 1) (hb : d236582 q = 1) : d23284 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d385, d23284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d385, d23284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro57485 (p : Pattern) (ha : d5355 p = 1) (hb : d236582 p = 1) : d23289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d236582 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57460 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d236582 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d236582 q = 1) : d23265 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d23265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d23265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d236582 q = 1) : d23266 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d23266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d23266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d236582 q = 1) : d23267 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d23267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d23267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d236582 q = 1) : d23289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d23289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d23289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57486 (p : Pattern) (ha : d74583 p = 1) (hb : d236582 p = 1) : d211129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d236582 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d236582 q = 1) : d23218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d23218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57474 q ha hb
    | true =>
      simp only [d297, d23218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d236582 q = 1) : d23219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d23219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d23219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d236582 q = 1) : d23220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d23220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d23220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d236582 q = 1) : d23221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d23221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d23221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d236582 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d236582 q = 1) : d23225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d23225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57475 q ha hb
    | true =>
      simp only [d304, d23225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d236582 q = 1) : d23226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d23226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d23226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d236582 q = 1) : d23227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d23227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d23227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d337 q = 1) (hb : d236582 q = 1) : d23249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d23249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57479 q ha hb
    | true =>
      simp only [d337, d23249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57467 q ha hb
  have h11 (q : Pattern) (ha : d4371 q = 1) (hb : d236582 q = 1) : d211120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4371, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d236582 q = 1) : d23269 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d23269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57480 q ha hb
    | true =>
      simp only [d4737, d23269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d236582 q = 1) : d23270 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d23270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d23270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d74576 q = 1) (hb : d236582 q = 1) : d211121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74576, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74576, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74577 q = 1) (hb : d236582 q = 1) : d211122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74577, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74577, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74578 q = 1) (hb : d236582 q = 1) : d211123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74578, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74578, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d236582 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d236582 q = 1) : d23276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d23276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57482 q ha hb
    | true =>
      simp only [d377, d23276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d236582 q = 1) : d23277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d23277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d23277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d236582 q = 1) : d23278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d23278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d23278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d236582 q = 1) : d23279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d23279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d23279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d236582 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d236582 q = 1) : d23281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d23281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57483 q ha hb
    | true =>
      simp only [d382, d23281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d236582 q = 1) : d23282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d23282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d23282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d236582 q = 1) : d23283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d23283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d23283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d386 q = 1) (hb : d236582 q = 1) : d23285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d23285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57484 q ha hb
    | true =>
      simp only [d386, d23285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57461 q ha hb
  have h27 (q : Pattern) (ha : d4376 q = 1) (hb : d236582 q = 1) : d211125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d4376, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d236582 q = 1) : d23290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d23290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57485 q ha hb
    | true =>
      simp only [d5356, d23290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d236582 q = 1) : d23291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d23291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d23291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d74580 q = 1) (hb : d236582 q = 1) : d211126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74580, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d74580, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74581 q = 1) (hb : d236582 q = 1) : d211127 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74581, d211127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74581, d211127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d74582 q = 1) (hb : d236582 q = 1) : d211128 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74582, d211128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74582, d211128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d74583 q = 1) (hb : d236582 q = 1) : d211129 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74583, d211129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74583, d211129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro57487 (p : Pattern) (ha : d74590 p = 1) (hb : d236582 p = 1) : d211136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d386 q = 1) (hb : d236582 q = 1) : d23285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d23285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57484 q ha hb
    | true =>
      simp only [d386, d23285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57461 q ha hb
  have h2 (q : Pattern) (ha : d4376 q = 1) (hb : d236582 q = 1) : d211125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4376, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d236582 q = 1) : d23290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d23290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57485 q ha hb
    | true =>
      simp only [d5356, d23290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d236582 q = 1) : d23291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d23291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d23291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74580 q = 1) (hb : d236582 q = 1) : d211126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74580, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74580, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74588 q = 1) (hb : d236582 q = 1) : d211134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74588, d211134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74588, d211134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74589 q = 1) (hb : d236582 q = 1) : d211135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74589, d211135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74589, d211135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74590 q = 1) (hb : d236582 q = 1) : d211136 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74590, d211136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74590, d211136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57488 (p : Pattern) (ha : d417 p = 1) (hb : d236582 p = 1) : d23315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d236582 q = 1) : d23310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57476 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d236582 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57476 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d236582 q = 1) : d23311 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d236582 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d236582 q = 1) : d23312 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d236582 q = 1) : d23313 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d236582 q = 1) : d12599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d12599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d12599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57458 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d236582 q = 1) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57458 q ha hb
    | true =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d236582 q = 1) : d12600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d12600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d12600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d236582 q = 1) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d236582 q = 1) : d12601 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d12601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d12601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d236582 q = 1) : d12602 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d12602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d12602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d236582 q = 1) : d23314 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d23314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d23314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69 q = 1) (hb : d236582 q = 1) : d69 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d230 q = 1) (hb : d236582 q = 1) : d12603 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d12603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d230, d12603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d417 q = 1) (hb : d236582 q = 1) : d23315 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d417, d23315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d417, d23315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro57489 (p : Pattern) (ha : d423 p = 1) (hb : d236582 p = 1) : d23321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d236582 q = 1) : d23316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57488 q ha hb
    | true =>
      simp only [d418, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57463 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d236582 q = 1) : d23317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d236582 q = 1) : d23318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d236582 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d236582 q = 1) : d23172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57463 q ha hb
    | true =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d236582 q = 1) : d23173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d236582 q = 1) : d23174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d421 q = 1) (hb : d236582 q = 1) : d23319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d421, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d236582 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d235 q = 1) (hb : d236582 q = 1) : d23175 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d23175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, d23175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d422 q = 1) (hb : d236582 q = 1) : d23320 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d422, d23320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d422, d23320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d423 q = 1) (hb : d236582 q = 1) : d23321 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d423, d23321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d423, d23321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro57490 (p : Pattern) (ha : d429 p = 1) (hb : d236582 p = 1) : d23327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d424 q = 1) (hb : d236582 q = 1) : d23322 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d424, d23322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57489 q ha hb
    | true =>
      simp only [d424, d23322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d425 q = 1) (hb : d236582 q = 1) : d23323 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d425, d23323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d425, d23323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d236582 q = 1) : d23178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57464 q ha hb
    | true =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d236582 q = 1) : d23179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d426 q = 1) (hb : d236582 q = 1) : d23324 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d426, d23324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d426, d23324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d427 q = 1) (hb : d236582 q = 1) : d23325 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d427, d23325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d427, d23325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d428 q = 1) (hb : d236582 q = 1) : d23326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d428, d23326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d428, d23326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d429 q = 1) (hb : d236582 q = 1) : d23327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d429, d23327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d429, d23327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro57491 (p : Pattern) (ha : d5377 p = 1) (hb : d236582 p = 1) : d23347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d236582 q = 1) : d23178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57464 q ha hb
    | true =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d236582 q = 1) : d23179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d236582 q = 1) : d23344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d23344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d23344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d236582 q = 1) : d23345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d23345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d23345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d236582 q = 1) : d23346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d23346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d23346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d236582 q = 1) : d23347 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d23347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d23347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro57492 (p : Pattern) (ha : d74599 p = 1) (hb : d236582 p = 1) : d211146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d430 q = 1) (hb : d236582 q = 1) : d23328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d430, d23328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57490 q ha hb
    | true =>
      simp only [d430, d23328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57465 q ha hb
  have h2 (q : Pattern) (ha : d4391 q = 1) (hb : d236582 q = 1) : d211142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d211142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4391, d211142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d236582 q = 1) : d23348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d23348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57491 q ha hb
    | true =>
      simp only [d5378, d23348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d236582 q = 1) : d23349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d23349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d23349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74596 q = 1) (hb : d236582 q = 1) : d211143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74596, d211143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74596, d211143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74597 q = 1) (hb : d236582 q = 1) : d211144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74597, d211144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74597, d211144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74598 q = 1) (hb : d236582 q = 1) : d211145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74598, d211145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74598, d211145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74599 q = 1) (hb : d236582 q = 1) : d211146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74599, d211146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74599, d211146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57493 (p : Pattern) (ha : d74605 p = 1) (hb : d236582 p = 1) : d211152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d236582 q = 1) : d23206 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d23206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d23206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57471 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d236582 q = 1) : d23207 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d23207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d23207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d236582 q = 1) : d23213 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d23213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57471 q ha hb
    | true =>
      simp only [d292, d23213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57472 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d236582 q = 1) : d23214 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d23214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d23214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d236582 q = 1) : d23215 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d23215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d23215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74584 q = 1) (hb : d236582 q = 1) : d211130 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74584, d211130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57481 q ha hb
    | true =>
      simp only [d74584, d211130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57486 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d236582 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d236582 q = 1) : d23298 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d23298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57473 q ha hb
    | true =>
      simp only [d398, d23298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74585 q = 1) (hb : d236582 q = 1) : d211131 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74585, d211131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74585, d211131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74586 q = 1) (hb : d236582 q = 1) : d211132 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74586, d211132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74586, d211132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d74587 q = 1) (hb : d236582 q = 1) : d211133 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74587, d211133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74587, d211133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74591 q = 1) (hb : d236582 q = 1) : d211137 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74591, d211137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74591, d211137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57487 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d236582 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d74592 q = 1) (hb : d236582 q = 1) : d211138 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74592, d211138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74592, d211138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74593 q = 1) (hb : d236582 q = 1) : d211139 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74593, d211139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74593, d211139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74594 q = 1) (hb : d236582 q = 1) : d211140 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74594, d211140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74594, d211140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d74595 q = 1) (hb : d236582 q = 1) : d211141 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74595, d211141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74595, d211141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d74600 q = 1) (hb : d236582 q = 1) : d211147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74600, d211147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74600, d211147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57492 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d236582 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d74601 q = 1) (hb : d236582 q = 1) : d211148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74601, d211148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74601, d211148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d74602 q = 1) (hb : d236582 q = 1) : d211149 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74602, d211149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74602, d211149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74603 q = 1) (hb : d236582 q = 1) : d211150 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74603, d211150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74603, d211150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74604 q = 1) (hb : d236582 q = 1) : d211151 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74604, d211151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d74604, d211151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d74605 q = 1) (hb : d236582 q = 1) : d211152 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74605, d211152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74605, d211152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro57494 (p : Pattern) (ha : d74611 p = 1) (hb : d236582 p = 1) : d211158 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d236582 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d236582 q = 1) : d211115 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57470 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d236582 q = 1) : d211116 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d236582 q = 1) : d211117 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d236582 q = 1) : d211118 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d236582 q = 1) : d211119 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74606 q = 1) (hb : d236582 q = 1) : d211153 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74606, d211153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74606, d211153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57493 q ha hb
  have h8 (q : Pattern) (ha : d74607 q = 1) (hb : d236582 q = 1) : d211154 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74607, d211154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74607, d211154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74608 q = 1) (hb : d236582 q = 1) : d211155 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74608, d211155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74608, d211155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74609 q = 1) (hb : d236582 q = 1) : d211156 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74609, d211156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74609, d211156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74610 q = 1) (hb : d236582 q = 1) : d211157 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74610, d211157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74610, d211157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74611 q = 1) (hb : d236582 q = 1) : d211158 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74611, d211158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74611, d211158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro57495 (p : Pattern) (ha : d477 p = 1) (hb : d236582 p = 1) : d23368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d236582 q = 1) : d23237 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57477 q ha hb
    | true =>
      simp only [d325, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57459 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d236582 q = 1) : d23238 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d236582 q = 1) : d23239 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d236582 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d236582 q = 1) : d23135 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57459 q ha hb
    | true =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d236582 q = 1) : d23136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d236582 q = 1) : d23137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d328 q = 1) (hb : d236582 q = 1) : d23240 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d328, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d236582 q = 1) : d23366 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d23366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d23366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d476 q = 1) (hb : d236582 q = 1) : d23367 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d476, d23367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d476, d23367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d477 q = 1) (hb : d236582 q = 1) : d23368 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d477, d23368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d477, d23368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro57496 (p : Pattern) (ha : d481 p = 1) (hb : d236582 p = 1) : d23372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d236582 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d236582 q = 1) : d23135 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57459 q ha hb
    | true =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d236582 q = 1) : d23136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d236582 q = 1) : d23137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d236582 q = 1) : d23366 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d23366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d23366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d236582 q = 1) : d23371 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d23371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d23371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d236582 q = 1) : d23372 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d23372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d23372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro57497 (p : Pattern) (ha : d487 p = 1) (hb : d236582 p = 1) : d23378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d236582 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57495 q ha hb
    | true =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d236582 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d236582 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57496 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d236582 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d236582 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d485 q = 1) (hb : d236582 q = 1) : d23376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d485, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d486 q = 1) (hb : d236582 q = 1) : d23377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d486, d23377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d486, d23377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d487 q = 1) (hb : d236582 q = 1) : d23378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d487, d23378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d487, d23378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro57498 (p : Pattern) (ha : d491 p = 1) (hb : d236582 p = 1) : d23382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d236582 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57496 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d236582 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d236582 q = 1) : d23379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d236582 q = 1) : d23380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d23380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d23380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d236582 q = 1) : d23381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d23381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d23381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d236582 q = 1) : d23382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d23382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d23382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro57499 (p : Pattern) (ha : d497 p = 1) (hb : d236582 p = 1) : d23388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d492 q = 1) (hb : d236582 q = 1) : d23383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57497 q ha hb
    | true =>
      simp only [d492, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57498 q ha hb
  have h2 (q : Pattern) (ha : d493 q = 1) (hb : d236582 q = 1) : d23384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d236582 q = 1) : d23385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d494, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d236582 q = 1) : d23386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d236582 q = 1) : d23387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d497 q = 1) (hb : d236582 q = 1) : d23388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, d23388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, d23388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
