import NetHack.Soko22Hazard87.AndIntroBlocks0042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro10750 (p : Pattern) (ha : d87204 p = 1) (hb : d89124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87103 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87199 q = 1) (hb : d89119 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d87199, d89119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87199, d89119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10749 q ha hb
  have h3 (q : Pattern) (ha : d87200 q = 1) (hb : d89120 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d87200, d89120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87200, d89120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87201 q = 1) (hb : d89121 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d87201, d89121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87201, d89121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87202 q = 1) (hb : d89122 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d87202, d89122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87202, d89122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87203 q = 1) (hb : d89123 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d87203, d89123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87203, d89123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87204 q = 1) (hb : d89124 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d87204, d89124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87204, d89124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10751 (p : Pattern) (ha : d87253 p = 1) (hb : d88305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87231 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87242 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d87053 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d87141 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87141, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10545 q ha hb
    | true =>
      simp only [d87141, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d87243 q = 1) (hb : d88301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87243, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d87243, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87249 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87250 q = 1) (hb : d88302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87250, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87250, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87251 q = 1) (hb : d88303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87251, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d87251, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87252 q = 1) (hb : d88304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87252, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87252, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87253 q = 1) (hb : d88305 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87253, d88305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87253, d88305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10752 (p : Pattern) (ha : d87272 p = 1) (hb : d88314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87225 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87231 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87242 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87053 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87141 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87141, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10545 q ha hb
    | true =>
      simp only [d87141, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87243 q = 1) (hb : d88301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87243, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d87243, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87249 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87250 q = 1) (hb : d88302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87250, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87250, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87251 q = 1) (hb : d88303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87251, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87251, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87252 q = 1) (hb : d88304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87252, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87252, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d87258 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87262 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d87264 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d87060 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d87157 q = 1) (hb : d88309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87157, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10547 q ha hb
    | true =>
      simp only [d87157, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d87265 q = 1) (hb : d88310 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87265, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d87265, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d87268 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d87269 q = 1) (hb : d88311 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87269, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87269, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d87270 q = 1) (hb : d88312 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87270, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d87270, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d87271 q = 1) (hb : d88313 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87271, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d87271, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d87272 q = 1) (hb : d88314 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87272, d88314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87272, d88314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro10753 (p : Pattern) (ha : d87281 p = 1) (hb : d89127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87264 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87060 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87157 q = 1) (hb : d88309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87157, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10547 q ha hb
    | true =>
      simp only [d87157, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87265 q = 1) (hb : d88310 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87265, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87265, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d87268 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d87269 q = 1) (hb : d88311 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87269, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87269, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d87279 q = 1) (hb : d88312 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87279, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87279, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87280 q = 1) (hb : d88313 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87280, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87280, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87281 q = 1) (hb : d89127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87281, d89127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87281, d89127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10754 (p : Pattern) (ha : d87186 p = 1) (hb : d88423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87181 q = 1) (hb : d88418 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87181, d88418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10571 q ha hb
    | true =>
      simp only [d87181, d88418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87182 q = 1) (hb : d88419 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87182, d88419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87182, d88419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87082 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87183 q = 1) (hb : d88420 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87183, d88420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87183, d88420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87184 q = 1) (hb : d88421 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87184, d88421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87184, d88421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87185 q = 1) (hb : d88422 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87185, d88422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87185, d88422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87186 q = 1) (hb : d88423 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87186, d88423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87186, d88423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10755 (p : Pattern) (ha : d87310 p = 1) (hb : d89137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87299 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87086 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87187 q = 1) (hb : d88424 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87187, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10754 q ha hb
    | true =>
      simp only [d87187, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87300 q = 1) (hb : d89133 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87300, d89133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87300, d89133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d87306 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d87307 q = 1) (hb : d89134 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87307, d89134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87307, d89134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d87308 q = 1) (hb : d89135 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87308, d89135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87308, d89135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87309 q = 1) (hb : d89136 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87309, d89136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87309, d89136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87310 q = 1) (hb : d89137 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87310, d89137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87310, d89137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10756 (p : Pattern) (ha : d87322 p = 1) (hb : d89143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87219 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87273 q = 1) (hb : d88315 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87273, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10751 q ha hb
    | true =>
      simp only [d87273, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10752 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87275 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87276 q = 1) (hb : d88316 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87276, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87276, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d87277 q = 1) (hb : d89125 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87277, d89125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87277, d89125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d87278 q = 1) (hb : d89126 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87278, d89126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87278, d89126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87282 q = 1) (hb : d89128 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87282, d89128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d87282, d89128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10753 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d87284 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d87285 q = 1) (hb : d89129 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87285, d89129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d87285, d89129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d87286 q = 1) (hb : d89130 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87286, d89130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87286, d89130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d87287 q = 1) (hb : d89131 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87287, d89131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87287, d89131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d87288 q = 1) (hb : d89132 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87288, d89132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87288, d89132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d87311 q = 1) (hb : d89138 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87311, d89138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d87311, d89138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10755 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d87317 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d87318 q = 1) (hb : d89139 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87318, d89139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87318, d89139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d87319 q = 1) (hb : d89140 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87319, d89140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87319, d89140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d87320 q = 1) (hb : d89141 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87320, d89141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d87320, d89141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d87321 q = 1) (hb : d89142 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87321, d89142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87321, d89142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d87322 q = 1) (hb : d89143 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d87322, d89143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87322, d89143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10757 (p : Pattern) (ha : d87328 p = 1) (hb : d89149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87323 q = 1) (hb : d89144 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d87323, d89144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87323, d89144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10756 q ha hb
  have h2 (q : Pattern) (ha : d87324 q = 1) (hb : d89145 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d87324, d89145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87324, d89145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87325 q = 1) (hb : d89146 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d87325, d89146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87325, d89146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87326 q = 1) (hb : d89147 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d87326, d89147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87326, d89147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87327 q = 1) (hb : d89148 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d87327, d89148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87327, d89148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87328 q = 1) (hb : d89149 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d87328, d89149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87328, d89149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10758 (p : Pattern) (ha : d87407 p = 1) (hb : d88456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87376 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87385 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87396 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d87349 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d87350 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87350, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10577 q ha hb
    | true =>
      simp only [d87350, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d87397 q = 1) (hb : d88452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87397, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d87397, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87403 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87404 q = 1) (hb : d88453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87404, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87404, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87405 q = 1) (hb : d88454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87405, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d87405, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87406 q = 1) (hb : d88455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87406, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87406, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87407 q = 1) (hb : d88456 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87407, d88456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87407, d88456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10759 (p : Pattern) (ha : d87428 p = 1) (hb : d88465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87385 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87349 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87350 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87350, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10577 q ha hb
    | true =>
      simp only [d87350, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87397 q = 1) (hb : d88452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87397, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d87397, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87403 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87404 q = 1) (hb : d88453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87404, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87404, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87405 q = 1) (hb : d88454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87405, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87405, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87406 q = 1) (hb : d88455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87406, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87406, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d87413 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87418 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d87420 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d87359 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d87360 q = 1) (hb : d88460 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87360, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10579 q ha hb
    | true =>
      simp only [d87360, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d87421 q = 1) (hb : d88461 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87421, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d87421, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d87424 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d87425 q = 1) (hb : d88462 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87425, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87425, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d87426 q = 1) (hb : d88463 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87426, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d87426, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d87427 q = 1) (hb : d88464 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87427, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d87427, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d87428 q = 1) (hb : d88465 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87428, d88465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87428, d88465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro10760 (p : Pattern) (ha : d87448 p = 1) (hb : d89153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87420 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87359 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87360 q = 1) (hb : d88460 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87360, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10579 q ha hb
    | true =>
      simp only [d87360, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87421 q = 1) (hb : d88461 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87421, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87421, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d87424 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d87425 q = 1) (hb : d88462 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87425, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87425, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d87446 q = 1) (hb : d88463 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87446, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87446, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87447 q = 1) (hb : d88464 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87447, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87447, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87448 q = 1) (hb : d89153 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87448, d89153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87448, d89153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10761 (p : Pattern) (ha : d87481 p = 1) (hb : d88574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87468 q = 1) (hb : d88569 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87468, d88569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10603 q ha hb
    | true =>
      simp only [d87468, d88569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87469 q = 1) (hb : d88570 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87469, d88570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87469, d88570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87477 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87478 q = 1) (hb : d88571 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87478, d88571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87478, d88571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87479 q = 1) (hb : d88572 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87479, d88572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87479, d88572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87480 q = 1) (hb : d88573 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87480, d88573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87480, d88573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87481 q = 1) (hb : d88574 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87481, d88574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87481, d88574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10762 (p : Pattern) (ha : d87498 p = 1) (hb : d89163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87482 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87486 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87487 q = 1) (hb : d88575 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87487, d88575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10761 q ha hb
    | true =>
      simp only [d87487, d88575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87488 q = 1) (hb : d89159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87488, d89159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87488, d89159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d87494 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d87495 q = 1) (hb : d89160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87495, d89160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87495, d89160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d87496 q = 1) (hb : d89161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87496, d89161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87496, d89161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87497 q = 1) (hb : d89162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87497, d89162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87497, d89162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87498 q = 1) (hb : d89163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87498, d89163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87498, d89163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10763 (p : Pattern) (ha : d87511 p = 1) (hb : d89169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87368 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87429 q = 1) (hb : d88466 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87429, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10758 q ha hb
    | true =>
      simp only [d87429, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10759 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87442 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87443 q = 1) (hb : d88467 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87443, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87443, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d87444 q = 1) (hb : d89151 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87444, d89151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87444, d89151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d87445 q = 1) (hb : d89152 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87445, d89152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87445, d89152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87449 q = 1) (hb : d89154 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87449, d89154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d87449, d89154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10760 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d87451 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d87452 q = 1) (hb : d89155 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87452, d89155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d87452, d89155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d87453 q = 1) (hb : d89156 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87453, d89156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87453, d89156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d87454 q = 1) (hb : d89157 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87454, d89157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87454, d89157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d87455 q = 1) (hb : d89158 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87455, d89158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87455, d89158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d87499 q = 1) (hb : d89164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87499, d89164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d87499, d89164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10762 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d87506 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d87507 q = 1) (hb : d89165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87507, d89165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87507, d89165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d87508 q = 1) (hb : d89166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87508, d89166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87508, d89166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d87509 q = 1) (hb : d89167 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87509, d89167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d87509, d89167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d87510 q = 1) (hb : d89168 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87510, d89168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87510, d89168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d87511 q = 1) (hb : d89169 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d87511, d89169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87511, d89169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10764 (p : Pattern) (ha : d87517 p = 1) (hb : d89175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87512 q = 1) (hb : d89170 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d87512, d89170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87512, d89170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10763 q ha hb
  have h2 (q : Pattern) (ha : d87513 q = 1) (hb : d89171 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d87513, d89171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87513, d89171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87514 q = 1) (hb : d89172 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d87514, d89172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87514, d89172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87515 q = 1) (hb : d89173 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d87515, d89173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87515, d89173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87516 q = 1) (hb : d89174 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d87516, d89174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87516, d89174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87517 q = 1) (hb : d89175 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d87517, d89175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87517, d89175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10765 (p : Pattern) (ha : d87597 p = 1) (hb : d88608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87586 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d87539 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d87540 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87540, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10609 q ha hb
    | true =>
      simp only [d87540, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d87587 q = 1) (hb : d88604 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87587, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d87587, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87593 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87594 q = 1) (hb : d88605 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87594, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87594, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87595 q = 1) (hb : d88606 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87595, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d87595, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87596 q = 1) (hb : d88607 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87596, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87596, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87597 q = 1) (hb : d88608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87597, d88608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87597, d88608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10766 (p : Pattern) (ha : d87618 p = 1) (hb : d88617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87566 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87586 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87539 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87540 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87540, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10609 q ha hb
    | true =>
      simp only [d87540, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87587 q = 1) (hb : d88604 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87587, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d87587, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87593 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87594 q = 1) (hb : d88605 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87594, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87594, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87595 q = 1) (hb : d88606 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87595, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87595, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87596 q = 1) (hb : d88607 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87596, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87596, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d87603 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87608 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d87610 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d87549 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d87550 q = 1) (hb : d88612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87550, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10611 q ha hb
    | true =>
      simp only [d87550, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d87611 q = 1) (hb : d88613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87611, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d87611, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d87614 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d87615 q = 1) (hb : d88614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87615, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87615, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d87616 q = 1) (hb : d88615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87616, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d87616, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d87617 q = 1) (hb : d88616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87617, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d87617, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d87618 q = 1) (hb : d88617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87618, d88617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87618, d88617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro10767 (p : Pattern) (ha : d87638 p = 1) (hb : d89180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87610 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87550 q = 1) (hb : d88612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87550, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10611 q ha hb
    | true =>
      simp only [d87550, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87611 q = 1) (hb : d88613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87611, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87611, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d87614 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d87615 q = 1) (hb : d88614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87615, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87615, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d87636 q = 1) (hb : d88615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87636, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87636, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87637 q = 1) (hb : d88616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87637, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87637, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87638 q = 1) (hb : d89180 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87638, d89180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87638, d89180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10768 (p : Pattern) (ha : d87671 p = 1) (hb : d88726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87658 q = 1) (hb : d88721 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87658, d88721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10635 q ha hb
    | true =>
      simp only [d87658, d88721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87659 q = 1) (hb : d88722 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87659, d88722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87659, d88722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87667 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87668 q = 1) (hb : d88723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87668, d88723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87668, d88723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87669 q = 1) (hb : d88724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87669, d88724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87669, d88724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87670 q = 1) (hb : d88725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87670, d88725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87670, d88725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87671 q = 1) (hb : d88726 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87671, d88726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87671, d88726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10769 (p : Pattern) (ha : d87688 p = 1) (hb : d89190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87672 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87676 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87677 q = 1) (hb : d88727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87677, d88727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10768 q ha hb
    | true =>
      simp only [d87677, d88727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87678 q = 1) (hb : d89186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87678, d89186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87678, d89186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d87684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d87685 q = 1) (hb : d89187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87685, d89187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87685, d89187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d87686 q = 1) (hb : d89188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87686, d89188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87686, d89188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87687 q = 1) (hb : d89189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87687, d89189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87687, d89189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87688 q = 1) (hb : d89190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87688, d89190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87688, d89190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10770 (p : Pattern) (ha : d87701 p = 1) (hb : d89196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87558 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87619 q = 1) (hb : d88618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87619, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10765 q ha hb
    | true =>
      simp only [d87619, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10766 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87632 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87633 q = 1) (hb : d88619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87633, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87633, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d87634 q = 1) (hb : d89178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87634, d89178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87634, d89178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d87635 q = 1) (hb : d89179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87635, d89179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87635, d89179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87639 q = 1) (hb : d89181 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87639, d89181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d87639, d89181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10767 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d87641 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d87642 q = 1) (hb : d89182 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87642, d89182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d87642, d89182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d87643 q = 1) (hb : d89183 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87643, d89183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87643, d89183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d87644 q = 1) (hb : d89184 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87644, d89184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87644, d89184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d87645 q = 1) (hb : d89185 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87645, d89185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87645, d89185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d87689 q = 1) (hb : d89191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87689, d89191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d87689, d89191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10769 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d87696 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d87697 q = 1) (hb : d89192 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87697, d89192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87697, d89192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d87698 q = 1) (hb : d89193 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87698, d89193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87698, d89193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d87699 q = 1) (hb : d89194 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87699, d89194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d87699, d89194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d87700 q = 1) (hb : d89195 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87700, d89195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87700, d89195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d87701 q = 1) (hb : d89196 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d87701, d89196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87701, d89196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10771 (p : Pattern) (ha : d87707 p = 1) (hb : d89202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87702 q = 1) (hb : d89197 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d87702, d89197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87702, d89197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10770 q ha hb
  have h2 (q : Pattern) (ha : d87703 q = 1) (hb : d89198 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d87703, d89198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87703, d89198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87704 q = 1) (hb : d89199 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d87704, d89199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87704, d89199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87705 q = 1) (hb : d89200 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d87705, d89200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87705, d89200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87706 q = 1) (hb : d89201 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d87706, d89201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87706, d89201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87707 q = 1) (hb : d89202 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d87707, d89202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87707, d89202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10772 (p : Pattern) (ha : d87788 p = 1) (hb : d88761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87766 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87777 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d87730 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d87731 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87731, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10641 q ha hb
    | true =>
      simp only [d87731, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d87778 q = 1) (hb : d88757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87778, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d87778, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87784 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87785 q = 1) (hb : d88758 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87785, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87785, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87786 q = 1) (hb : d88759 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87786, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d87786, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87787 q = 1) (hb : d88760 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87787, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87787, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87788 q = 1) (hb : d88761 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87788, d88761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87788, d88761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10773 (p : Pattern) (ha : d87809 p = 1) (hb : d88770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87757 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87777 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87730 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87731 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87731, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10641 q ha hb
    | true =>
      simp only [d87731, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87778 q = 1) (hb : d88757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87778, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d87778, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87784 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87785 q = 1) (hb : d88758 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87785, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87785, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87786 q = 1) (hb : d88759 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87786, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87786, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87787 q = 1) (hb : d88760 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87787, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87787, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d87794 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87799 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d87801 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d87740 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d87741 q = 1) (hb : d88765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87741, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10643 q ha hb
    | true =>
      simp only [d87741, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d87802 q = 1) (hb : d88766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87802, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d87802, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d87805 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d87806 q = 1) (hb : d88767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87806, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87806, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d87807 q = 1) (hb : d88768 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87807, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d87807, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d87808 q = 1) (hb : d88769 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87808, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d87808, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d87809 q = 1) (hb : d88770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87809, d88770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87809, d88770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro10774 (p : Pattern) (ha : d87829 p = 1) (hb : d89208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87740 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87741 q = 1) (hb : d88765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87741, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10643 q ha hb
    | true =>
      simp only [d87741, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87802 q = 1) (hb : d88766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87802, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87802, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d87805 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d87806 q = 1) (hb : d88767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87806, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87806, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d87827 q = 1) (hb : d88768 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87827, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87827, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87828 q = 1) (hb : d88769 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87828, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87828, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87829 q = 1) (hb : d89208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87829, d89208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87829, d89208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10775 (p : Pattern) (ha : d87862 p = 1) (hb : d88879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87849 q = 1) (hb : d88874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d87849, d88874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10667 q ha hb
    | true =>
      simp only [d87849, d88874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d87850 q = 1) (hb : d88875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d87850, d88875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87850, d88875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87858 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87859 q = 1) (hb : d88876 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d87859, d88876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d87859, d88876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87860 q = 1) (hb : d88877 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d87860, d88877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87860, d88877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d87861 q = 1) (hb : d88878 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d87861, d88878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87861, d88878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d87862 q = 1) (hb : d88879 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d87862, d88879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87862, d88879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10776 (p : Pattern) (ha : d87879 p = 1) (hb : d89218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87863 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87867 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87868 q = 1) (hb : d88880 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87868, d88880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10775 q ha hb
    | true =>
      simp only [d87868, d88880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87869 q = 1) (hb : d89214 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87869, d89214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87869, d89214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d87875 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d87876 q = 1) (hb : d89215 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87876, d89215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87876, d89215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d87877 q = 1) (hb : d89216 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87877, d89216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87877, d89216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d87878 q = 1) (hb : d89217 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87878, d89217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87878, d89217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87879 q = 1) (hb : d89218 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87879, d89218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87879, d89218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10777 (p : Pattern) (ha : d87892 p = 1) (hb : d89224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87810 q = 1) (hb : d88771 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87810, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10772 q ha hb
    | true =>
      simp only [d87810, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10773 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87823 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87824 q = 1) (hb : d88772 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87824, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d87824, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d87825 q = 1) (hb : d89206 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87825, d89206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87825, d89206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d87826 q = 1) (hb : d89207 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87826, d89207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87826, d89207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87830 q = 1) (hb : d89209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87830, d89209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d87830, d89209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10774 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d87832 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d87833 q = 1) (hb : d89210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87833, d89210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d87833, d89210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d87834 q = 1) (hb : d89211 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87834, d89211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d87834, d89211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d87835 q = 1) (hb : d89212 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87835, d89212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d87835, d89212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d87836 q = 1) (hb : d89213 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87836, d89213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87836, d89213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d87880 q = 1) (hb : d89219 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d87880, d89219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d87880, d89219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10776 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d87887 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d87888 q = 1) (hb : d89220 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d87888, d89220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d87888, d89220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d87889 q = 1) (hb : d89221 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d87889, d89221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87889, d89221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d87890 q = 1) (hb : d89222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d87890, d89222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d87890, d89222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d87891 q = 1) (hb : d89223 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d87891, d89223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d87891, d89223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d87892 q = 1) (hb : d89224 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d87892, d89224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d87892, d89224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10778 (p : Pattern) (ha : d87898 p = 1) (hb : d89230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d87893 q = 1) (hb : d89225 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d87893, d89225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87893, d89225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10777 q ha hb
  have h2 (q : Pattern) (ha : d87894 q = 1) (hb : d89226 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d87894, d89226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87894, d89226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d87895 q = 1) (hb : d89227 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d87895, d89227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87895, d89227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87896 q = 1) (hb : d89228 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d87896, d89228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87896, d89228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d87897 q = 1) (hb : d89229 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d87897, d89229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87897, d89229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87898 q = 1) (hb : d89230 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d87898, d89230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87898, d89230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10779 (p : Pattern) (ha : d87980 p = 1) (hb : d88915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87949 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87958 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87969 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d87922 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d87923 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87923, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10673 q ha hb
    | true =>
      simp only [d87923, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d87970 q = 1) (hb : d88911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87970, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d87970, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d87976 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d87977 q = 1) (hb : d88912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87977, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87977, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d87978 q = 1) (hb : d88913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87978, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d87978, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87979 q = 1) (hb : d88914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87979, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87979, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d87980 q = 1) (hb : d88915 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d87980, d88915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87980, d88915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10780 (p : Pattern) (ha : d88001 p = 1) (hb : d88924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87949 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87958 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87969 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d87922 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d87923 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87923, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10673 q ha hb
    | true =>
      simp only [d87923, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d87970 q = 1) (hb : d88911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87970, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d87970, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d87976 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d87977 q = 1) (hb : d88912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87977, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d87977, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d87978 q = 1) (hb : d88913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87978, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87978, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87979 q = 1) (hb : d88914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d87979, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d87979, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d87986 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d87991 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d87993 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d87932 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d87933 q = 1) (hb : d88919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87933, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10675 q ha hb
    | true =>
      simp only [d87933, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d87994 q = 1) (hb : d88920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87994, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d87994, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d87997 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d87998 q = 1) (hb : d88921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87998, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d87998, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d87999 q = 1) (hb : d88922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87999, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d87999, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d88000 q = 1) (hb : d88923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88000, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d88000, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d88001 q = 1) (hb : d88924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88001, d88924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88001, d88924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro10781 (p : Pattern) (ha : d88021 p = 1) (hb : d89237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d87993 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d87932 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d87933 q = 1) (hb : d88919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d87933, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10675 q ha hb
    | true =>
      simp only [d87933, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d87994 q = 1) (hb : d88920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d87994, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87994, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d87997 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d87998 q = 1) (hb : d88921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d87998, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d87998, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d88019 q = 1) (hb : d88922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88019, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88019, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88020 q = 1) (hb : d88923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88020, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88020, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88021 q = 1) (hb : d89237 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88021, d89237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88021, d89237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10782 (p : Pattern) (ha : d88054 p = 1) (hb : d89033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88041 q = 1) (hb : d89028 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d88041, d89028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10699 q ha hb
    | true =>
      simp only [d88041, d89028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88042 q = 1) (hb : d89029 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d88042, d89029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88042, d89029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88050 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88051 q = 1) (hb : d89030 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88051, d89030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88051, d89030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d88052 q = 1) (hb : d89031 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d88052, d89031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88052, d89031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88053 q = 1) (hb : d89032 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d88053, d89032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88053, d89032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d88054 q = 1) (hb : d89033 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d88054, d89033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88054, d89033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro10783 (p : Pattern) (ha : d88071 p = 1) (hb : d89247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d88055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88059 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88060 q = 1) (hb : d89034 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d88060, d89034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10782 q ha hb
    | true =>
      simp only [d88060, d89034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88061 q = 1) (hb : d89243 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88061, d89243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d88061, d89243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d88067 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88068 q = 1) (hb : d89244 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88068, d89244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88068, d89244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d88069 q = 1) (hb : d89245 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88069, d89245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88069, d89245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88070 q = 1) (hb : d89246 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88070, d89246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88070, d89246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88071 q = 1) (hb : d89247 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88071, d89247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88071, d89247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10784 (p : Pattern) (ha : d88084 p = 1) (hb : d89253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d87941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88002 q = 1) (hb : d88925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88002, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10779 q ha hb
    | true =>
      simp only [d88002, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10780 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88015 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88016 q = 1) (hb : d88926 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88016, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88016, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88017 q = 1) (hb : d89235 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d88017, d89235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88017, d89235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88018 q = 1) (hb : d89236 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d88018, d89236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88018, d89236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88022 q = 1) (hb : d89238 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88022, d89238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d88022, d89238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10781 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d88024 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d88025 q = 1) (hb : d89239 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88025, d89239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d88025, d89239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d88026 q = 1) (hb : d89240 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d88026, d89240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88026, d89240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d88027 q = 1) (hb : d89241 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d88027, d89241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88027, d89241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d88028 q = 1) (hb : d89242 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d88028, d89242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88028, d89242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d88072 q = 1) (hb : d89248 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88072, d89248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d88072, d89248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10783 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d88079 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d88080 q = 1) (hb : d89249 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88080, d89249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88080, d89249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d88081 q = 1) (hb : d89250 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d88081, d89250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d88081, d89250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d88082 q = 1) (hb : d89251 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d88082, d89251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d88082, d89251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d88083 q = 1) (hb : d89252 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d88083, d89252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d88083, d89252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d88084 q = 1) (hb : d89253 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d88084, d89253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d88084, d89253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10785 (p : Pattern) (ha : d88090 p = 1) (hb : d89259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88085 q = 1) (hb : d89254 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d88085, d89254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88085, d89254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10784 q ha hb
  have h2 (q : Pattern) (ha : d88086 q = 1) (hb : d89255 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d88086, d89255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88086, d89255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88087 q = 1) (hb : d89256 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d88087, d89256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88087, d89256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88088 q = 1) (hb : d89257 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d88088, d89257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88088, d89257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88089 q = 1) (hb : d89258 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d88089, d89258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88089, d89258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88090 q = 1) (hb : d89259 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d88090, d89259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88090, d89259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10786 (p : Pattern) (ha : d88096 p = 1) (hb : d89265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d87329 q = 1) (hb : d89150 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d87329, d89150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10750 q ha hb
    | true =>
      simp only [d87329, d89150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10757 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d87518 q = 1) (hb : d89176 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d87518, d89176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87518, d89176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10764 q ha hb
  have h3 (q : Pattern) (ha : d87519 q = 1) (hb : d89177 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d87519, d89177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87519, d89177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d87708 q = 1) (hb : d89203 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d87708, d89203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87708, d89203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10771 q ha hb
  have h5 (q : Pattern) (ha : d87709 q = 1) (hb : d89204 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d87709, d89204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87709, d89204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87710 q = 1) (hb : d89205 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d87710, d89205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d87710, d89205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d87899 q = 1) (hb : d89231 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d87899, d89231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87899, d89231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10778 q ha hb
  have h8 (q : Pattern) (ha : d87900 q = 1) (hb : d89232 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d87900, d89232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87900, d89232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d87901 q = 1) (hb : d89233 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d87901, d89233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d87901, d89233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d87902 q = 1) (hb : d89234 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d87902, d89234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d87902, d89234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d88091 q = 1) (hb : d89260 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d88091, d89260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d88091, d89260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10785 q ha hb
  have h12 (q : Pattern) (ha : d88092 q = 1) (hb : d89261 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d88092, d89261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d88092, d89261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d88093 q = 1) (hb : d89262 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d88093, d89262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d88093, d89262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d88094 q = 1) (hb : d89263 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d88094, d89263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d88094, d89263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d88095 q = 1) (hb : d89264 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d88095, d89264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88095, d89264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88096 q = 1) (hb : d89265 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d88096, d89265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d88096, d89265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro10787 (p : Pattern) (ha : d88102 p = 1) (hb : d89271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88097 q = 1) (hb : d89266 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d88097, d89266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10786 q ha hb
    | true =>
      simp only [d88097, d89266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88098 q = 1) (hb : d89267 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d88098, d89267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88098, d89267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88099 q = 1) (hb : d89268 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d88099, d89268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88099, d89268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88100 q = 1) (hb : d89269 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d88100, d89269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88100, d89269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88101 q = 1) (hb : d89270 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d88101, d89270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88101, d89270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88102 q = 1) (hb : d89271 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d88102, d89271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88102, d89271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10788 (p : Pattern) (ha : d88108 p = 1) (hb : d89277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88103 q = 1) (hb : d89272 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d88103, d89272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10787 q ha hb
    | true =>
      simp only [d88103, d89272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88104 q = 1) (hb : d89273 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d88104, d89273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88104, d89273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88105 q = 1) (hb : d89274 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d88105, d89274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88105, d89274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88106 q = 1) (hb : d89275 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d88106, d89275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88106, d89275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88107 q = 1) (hb : d89276 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d88107, d89276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88107, d89276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88108 q = 1) (hb : d89277 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d88108, d89277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88108, d89277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10789 (p : Pattern) (ha : d88114 p = 1) (hb : d89283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88109 q = 1) (hb : d89278 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d88109, d89278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10788 q ha hb
    | true =>
      simp only [d88109, d89278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88110 q = 1) (hb : d89279 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d88110, d89279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88110, d89279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88111 q = 1) (hb : d89280 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d88111, d89280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88111, d89280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88112 q = 1) (hb : d89281 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d88112, d89281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88112, d89281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88113 q = 1) (hb : d89282 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d88113, d89282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88113, d89282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88114 q = 1) (hb : d89283 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d88114, d89283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88114, d89283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10790 (p : Pattern) (ha : d88120 p = 1) (hb : d89289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88115 q = 1) (hb : d89284 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d88115, d89284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10789 q ha hb
    | true =>
      simp only [d88115, d89284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88116 q = 1) (hb : d89285 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d88116, d89285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88116, d89285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88117 q = 1) (hb : d89286 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d88117, d89286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88117, d89286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88118 q = 1) (hb : d89287 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d88118, d89287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88118, d89287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88119 q = 1) (hb : d89288 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d88119, d89288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88119, d89288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88120 q = 1) (hb : d89289 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d88120, d89289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88120, d89289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10791 (p : Pattern) (ha : d88126 p = 1) (hb : d89295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88121 q = 1) (hb : d89290 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d88121, d89290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10790 q ha hb
    | true =>
      simp only [d88121, d89290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88122 q = 1) (hb : d89291 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d88122, d89291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88122, d89291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88123 q = 1) (hb : d89292 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d88123, d89292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88123, d89292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88124 q = 1) (hb : d89293 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d88124, d89293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88124, d89293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88125 q = 1) (hb : d89294 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d88125, d89294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88125, d89294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88126 q = 1) (hb : d89295 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d88126, d89295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88126, d89295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10792 (p : Pattern) (ha : d88132 p = 1) (hb : d89301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88127 q = 1) (hb : d89296 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d88127, d89296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10791 q ha hb
    | true =>
      simp only [d88127, d89296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88128 q = 1) (hb : d89297 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d88128, d89297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88128, d89297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88129 q = 1) (hb : d89298 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d88129, d89298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88129, d89298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88130 q = 1) (hb : d89299 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d88130, d89299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88130, d89299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88131 q = 1) (hb : d89300 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d88131, d89300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88131, d89300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88132 q = 1) (hb : d89301 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d88132, d89301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88132, d89301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10793 (p : Pattern) (ha : d88138 p = 1) (hb : d89307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88133 q = 1) (hb : d89302 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d88133, d89302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10792 q ha hb
    | true =>
      simp only [d88133, d89302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d88134 q = 1) (hb : d89303 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d88134, d89303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88134, d89303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88135 q = 1) (hb : d89304 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d88135, d89304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88135, d89304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d88136 q = 1) (hb : d89305 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d88136, d89305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88136, d89305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88137 q = 1) (hb : d89306 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d88137, d89306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88137, d89306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d88138 q = 1) (hb : d89307 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d88138, d89307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88138, d89307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10794 (p : Pattern) (ha : d88199 p = 1) (hb : d89312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85805 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d85811 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85822 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88195 q = 1) (hb : d89308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88195, d89308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88195, d89308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d85736 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d88196 q = 1) (hb : d89309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88196, d89309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88196, d89309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88197 q = 1) (hb : d89310 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88197, d89310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88197, d89310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88198 q = 1) (hb : d89311 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88198, d89311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88198, d89311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88199 q = 1) (hb : d89312 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88199, d89312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88199, d89312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10795 (p : Pattern) (ha : d88206 p = 1) (hb : d89317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85805 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d85822 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88195 q = 1) (hb : d89308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88195, d89308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88195, d89308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85736 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88196 q = 1) (hb : d89309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88196, d89309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88196, d89309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88197 q = 1) (hb : d89310 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88197, d89310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88197, d89310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88198 q = 1) (hb : d89311 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88198, d89311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88198, d89311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85843 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d85847 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d85849 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88202 q = 1) (hb : d89313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88202, d89313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88202, d89313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d85743 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d88203 q = 1) (hb : d89314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88203, d89314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88203, d89314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88204 q = 1) (hb : d89315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88204, d89315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88204, d89315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88205 q = 1) (hb : d89316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88205, d89316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88205, d89316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d88206 q = 1) (hb : d89317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88206, d89317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88206, d89317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10796 (p : Pattern) (ha : d89102 p = 1) (hb : d89324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85849 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88202 q = 1) (hb : d89313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88202, d89313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88202, d89313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85743 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88203 q = 1) (hb : d89314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88203, d89314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88203, d89314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88204 q = 1) (hb : d89322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88204, d89322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88204, d89322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88205 q = 1) (hb : d89323 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88205, d89323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88205, d89323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89102 q = 1) (hb : d89324 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89102, d89324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89102, d89324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10797 (p : Pattern) (ha : d89112 p = 1) (hb : d89334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88178 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d89108 q = 1) (hb : d89330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89108, d89330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89108, d89330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85769 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89109 q = 1) (hb : d89331 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89109, d89331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89109, d89331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89110 q = 1) (hb : d89332 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89110, d89332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89110, d89332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89111 q = 1) (hb : d89333 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89111, d89333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89111, d89333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89112 q = 1) (hb : d89334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89112, d89334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89112, d89334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10798 (p : Pattern) (ha : d89118 p = 1) (hb : d89340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85799 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88207 q = 1) (hb : d89318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88207, d89318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10794 q ha hb
    | true =>
      simp only [d88207, d89318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10795 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d85859 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88208 q = 1) (hb : d89319 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88208, d89319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88208, d89319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89100 q = 1) (hb : d89320 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89100, d89320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89100, d89320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89101 q = 1) (hb : d89321 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89101, d89321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89101, d89321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89103 q = 1) (hb : d89325 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89103, d89325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89103, d89325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10796 q ha hb
  have h8 (q : Pattern) (ha : d89104 q = 1) (hb : d89326 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89104, d89326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89104, d89326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89105 q = 1) (hb : d89327 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89105, d89327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89105, d89327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89106 q = 1) (hb : d89328 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89106, d89328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89106, d89328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89107 q = 1) (hb : d89329 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89107, d89329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89107, d89329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89113 q = 1) (hb : d89335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89113, d89335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89113, d89335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10797 q ha hb
  have h13 (q : Pattern) (ha : d89114 q = 1) (hb : d89336 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89114, d89336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89114, d89336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89115 q = 1) (hb : d89337 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89115, d89337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89115, d89337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89116 q = 1) (hb : d89338 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89116, d89338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89116, d89338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89117 q = 1) (hb : d89339 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89117, d89339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89117, d89339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89118 q = 1) (hb : d89340 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89118, d89340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89118, d89340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro10799 (p : Pattern) (ha : d89124 p = 1) (hb : d89346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85784 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d89119 q = 1) (hb : d89341 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89119, d89341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89119, d89341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10798 q ha hb
  have h3 (q : Pattern) (ha : d89120 q = 1) (hb : d89342 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89120, d89342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89120, d89342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89121 q = 1) (hb : d89343 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89121, d89343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89121, d89343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89122 q = 1) (hb : d89344 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89122, d89344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89122, d89344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89123 q = 1) (hb : d89345 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89123, d89345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89123, d89345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89124 q = 1) (hb : d89346 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89124, d89346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89124, d89346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro10800 (p : Pattern) (ha : d88305 p = 1) (hb : d89351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85930 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d85936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85947 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88301 q = 1) (hb : d89347 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88301, d89347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88301, d89347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d85965 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d88302 q = 1) (hb : d89348 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88302, d89348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88302, d89348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88303 q = 1) (hb : d89349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88303, d89349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88303, d89349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88304 q = 1) (hb : d89350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88304, d89350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88304, d89350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88305 q = 1) (hb : d89351 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88305, d89351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88305, d89351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10801 (p : Pattern) (ha : d88314 p = 1) (hb : d89356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85930 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85936 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d85947 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88301 q = 1) (hb : d89347 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88301, d89347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88301, d89347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88302 q = 1) (hb : d89348 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88302, d89348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88302, d89348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88303 q = 1) (hb : d89349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88303, d89349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88303, d89349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88304 q = 1) (hb : d89350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88304, d89350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88304, d89350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85974 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d85978 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d85980 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88309 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88310 q = 1) (hb : d89352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88310, d89352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88310, d89352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d85986 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d88311 q = 1) (hb : d89353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88311, d89353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88311, d89353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88312 q = 1) (hb : d89354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88312, d89354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88312, d89354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88313 q = 1) (hb : d89355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88313, d89355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88313, d89355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d88314 q = 1) (hb : d89356 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88314, d89356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88314, d89356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10802 (p : Pattern) (ha : d89127 p = 1) (hb : d89363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88309 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88310 q = 1) (hb : d89352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88310, d89352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88310, d89352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85986 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88311 q = 1) (hb : d89353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88311, d89353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88311, d89353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88312 q = 1) (hb : d89361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88312, d89361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88312, d89361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88313 q = 1) (hb : d89362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88313, d89362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88313, d89362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89127 q = 1) (hb : d89363 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89127, d89363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89127, d89363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10803 (p : Pattern) (ha : d89137 p = 1) (hb : d89373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88424 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d89133 q = 1) (hb : d89369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89133, d89369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89133, d89369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d86035 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89134 q = 1) (hb : d89370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89134, d89370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89134, d89370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89135 q = 1) (hb : d89371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89135, d89371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89135, d89371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89136 q = 1) (hb : d89372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89136, d89372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89136, d89372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89137 q = 1) (hb : d89373 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89137, d89373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89137, d89373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10804 (p : Pattern) (ha : d89143 p = 1) (hb : d89379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85924 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88315 q = 1) (hb : d89357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88315, d89357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10800 q ha hb
    | true =>
      simp only [d88315, d89357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10801 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d85993 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88316 q = 1) (hb : d89358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88316, d89358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88316, d89358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89125 q = 1) (hb : d89359 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89125, d89359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89125, d89359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89126 q = 1) (hb : d89360 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89126, d89360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89126, d89360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89128 q = 1) (hb : d89364 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89128, d89364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89128, d89364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10802 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d86002 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d89129 q = 1) (hb : d89365 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89129, d89365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89129, d89365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d89130 q = 1) (hb : d89366 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89130, d89366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89130, d89366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89131 q = 1) (hb : d89367 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89131, d89367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d89131, d89367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d89132 q = 1) (hb : d89368 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89132, d89368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89132, d89368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d89138 q = 1) (hb : d89374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89138, d89374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89138, d89374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10803 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d86046 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d89139 q = 1) (hb : d89375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89139, d89375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89139, d89375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d89140 q = 1) (hb : d89376 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89140, d89376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89140, d89376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89141 q = 1) (hb : d89377 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89141, d89377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d89141, d89377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d89142 q = 1) (hb : d89378 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89142, d89378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d89142, d89378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d89143 q = 1) (hb : d89379 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89143, d89379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89143, d89379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10805 (p : Pattern) (ha : d89149 p = 1) (hb : d89385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89144 q = 1) (hb : d89380 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89144, d89380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89144, d89380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10804 q ha hb
  have h2 (q : Pattern) (ha : d89145 q = 1) (hb : d89381 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89145, d89381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89145, d89381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89146 q = 1) (hb : d89382 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89146, d89382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89146, d89382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89147 q = 1) (hb : d89383 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89147, d89383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89147, d89383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89148 q = 1) (hb : d89384 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89148, d89384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89148, d89384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89149 q = 1) (hb : d89385 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89149, d89385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89149, d89385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10806 (p : Pattern) (ha : d88456 p = 1) (hb : d89391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d86114 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d86125 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88452 q = 1) (hb : d89387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88452, d89387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88452, d89387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d86153 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d88453 q = 1) (hb : d89388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88453, d89388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88453, d89388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88454 q = 1) (hb : d89389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88454, d89389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88454, d89389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88455 q = 1) (hb : d89390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88455, d89390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88455, d89390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88456 q = 1) (hb : d89391 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88456, d89391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88456, d89391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10807 (p : Pattern) (ha : d88465 p = 1) (hb : d89396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d86105 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86114 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d86125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88452 q = 1) (hb : d89387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88452, d89387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88452, d89387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d86153 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88453 q = 1) (hb : d89388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88453, d89388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88453, d89388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88454 q = 1) (hb : d89389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88454, d89389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88454, d89389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88455 q = 1) (hb : d89390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88455, d89390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88455, d89390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d86163 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d86168 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d86170 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88460 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88461 q = 1) (hb : d89392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88461, d89392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88461, d89392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d86177 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d88462 q = 1) (hb : d89393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88462, d89393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88462, d89393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88463 q = 1) (hb : d89394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88463, d89394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88463, d89394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88464 q = 1) (hb : d89395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88464, d89395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88464, d89395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d88465 q = 1) (hb : d89396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88465, d89396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88465, d89396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10808 (p : Pattern) (ha : d89153 p = 1) (hb : d89403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86170 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88460 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88461 q = 1) (hb : d89392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88461, d89392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88461, d89392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d86177 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88462 q = 1) (hb : d89393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88462, d89393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88462, d89393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88463 q = 1) (hb : d89401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88463, d89401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88463, d89401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88464 q = 1) (hb : d89402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88464, d89402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88464, d89402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89153 q = 1) (hb : d89403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89153, d89403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89153, d89403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10809 (p : Pattern) (ha : d89163 p = 1) (hb : d89413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86235 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d89159 q = 1) (hb : d89409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89159, d89409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89159, d89409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d86263 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89160 q = 1) (hb : d89410 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89160, d89410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89160, d89410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89161 q = 1) (hb : d89411 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89161, d89411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89161, d89411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89162 q = 1) (hb : d89412 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89162, d89412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89162, d89412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89163 q = 1) (hb : d89413 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89163, d89413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89163, d89413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10810 (p : Pattern) (ha : d89169 p = 1) (hb : d89419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d86097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88466 q = 1) (hb : d89397 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88466, d89397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10806 q ha hb
    | true =>
      simp only [d88466, d89397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10807 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d86195 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88467 q = 1) (hb : d89398 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88467, d89398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88467, d89398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89151 q = 1) (hb : d89399 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89151, d89399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89151, d89399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89152 q = 1) (hb : d89400 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89152, d89400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89152, d89400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89154 q = 1) (hb : d89404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89154, d89404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89154, d89404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10808 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d86204 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d89155 q = 1) (hb : d89405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89155, d89405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89155, d89405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d89156 q = 1) (hb : d89406 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89156, d89406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89156, d89406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89157 q = 1) (hb : d89407 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89157, d89407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d89157, d89407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d89158 q = 1) (hb : d89408 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89158, d89408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89158, d89408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d89164 q = 1) (hb : d89414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89164, d89414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89164, d89414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10809 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d86279 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d89165 q = 1) (hb : d89415 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89165, d89415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89165, d89415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d89166 q = 1) (hb : d89416 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89166, d89416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89166, d89416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89167 q = 1) (hb : d89417 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89167, d89417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d89167, d89417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d89168 q = 1) (hb : d89418 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89168, d89418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d89168, d89418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d89169 q = 1) (hb : d89419 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89169, d89419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89169, d89419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10811 (p : Pattern) (ha : d89175 p = 1) (hb : d89425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89170 q = 1) (hb : d89420 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89170, d89420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89170, d89420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10810 q ha hb
  have h2 (q : Pattern) (ha : d89171 q = 1) (hb : d89421 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89171, d89421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89171, d89421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89172 q = 1) (hb : d89422 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89172, d89422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89172, d89422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89173 q = 1) (hb : d89423 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89173, d89423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89173, d89423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89174 q = 1) (hb : d89424 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89174, d89424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89174, d89424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89175 q = 1) (hb : d89425 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89175, d89425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89175, d89425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10812 (p : Pattern) (ha : d88608 p = 1) (hb : d89432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86339 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d86348 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d86359 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88604 q = 1) (hb : d89428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88604, d89428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88604, d89428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d86387 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d88605 q = 1) (hb : d89429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88605, d89429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88605, d89429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88606 q = 1) (hb : d89430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88606, d89430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88606, d89430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88607 q = 1) (hb : d89431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88607, d89431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88607, d89431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88608 q = 1) (hb : d89432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88608, d89432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88608, d89432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10813 (p : Pattern) (ha : d88617 p = 1) (hb : d89437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d86339 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86348 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d86359 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88604 q = 1) (hb : d89428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88604, d89428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88604, d89428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d86387 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88605 q = 1) (hb : d89429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88605, d89429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88605, d89429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88606 q = 1) (hb : d89430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88606, d89430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88606, d89430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88607 q = 1) (hb : d89431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88607, d89431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88607, d89431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d86397 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d86402 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d86404 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88612 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88613 q = 1) (hb : d89433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88613, d89433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88613, d89433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d86411 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d88614 q = 1) (hb : d89434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88614, d89434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88614, d89434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88615 q = 1) (hb : d89435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88615, d89435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88615, d89435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88616 q = 1) (hb : d89436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88616, d89436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88616, d89436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d88617 q = 1) (hb : d89437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88617, d89437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88617, d89437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10814 (p : Pattern) (ha : d89180 p = 1) (hb : d89444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86404 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88612 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88613 q = 1) (hb : d89433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88613, d89433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88613, d89433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d86411 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88614 q = 1) (hb : d89434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88614, d89434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88614, d89434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88615 q = 1) (hb : d89442 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88615, d89442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88615, d89442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88616 q = 1) (hb : d89443 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88616, d89443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88616, d89443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89180 q = 1) (hb : d89444 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89180, d89444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89180, d89444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10815 (p : Pattern) (ha : d89190 p = 1) (hb : d89454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86469 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d89186 q = 1) (hb : d89450 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89186, d89450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89186, d89450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d86497 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89187 q = 1) (hb : d89451 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89187, d89451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89187, d89451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89188 q = 1) (hb : d89452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89188, d89452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89188, d89452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89189 q = 1) (hb : d89453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89189, d89453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89189, d89453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89190 q = 1) (hb : d89454 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89190, d89454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89190, d89454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10816 (p : Pattern) (ha : d89196 p = 1) (hb : d89460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d86331 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88618 q = 1) (hb : d89438 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88618, d89438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10812 q ha hb
    | true =>
      simp only [d88618, d89438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10813 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d86429 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88619 q = 1) (hb : d89439 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88619, d89439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88619, d89439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89178 q = 1) (hb : d89440 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89178, d89440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89178, d89440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89179 q = 1) (hb : d89441 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89179, d89441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89179, d89441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89181 q = 1) (hb : d89445 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89181, d89445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89181, d89445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10814 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d86438 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d89182 q = 1) (hb : d89446 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89182, d89446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89182, d89446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d89183 q = 1) (hb : d89447 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89183, d89447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89183, d89447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89184 q = 1) (hb : d89448 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89184, d89448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d89184, d89448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d89185 q = 1) (hb : d89449 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89185, d89449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89185, d89449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d89191 q = 1) (hb : d89455 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89191, d89455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89191, d89455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10815 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d86513 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d89192 q = 1) (hb : d89456 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89192, d89456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89192, d89456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d89193 q = 1) (hb : d89457 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89193, d89457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89193, d89457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89194 q = 1) (hb : d89458 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89194, d89458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d89194, d89458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d89195 q = 1) (hb : d89459 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89195, d89459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d89195, d89459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d89196 q = 1) (hb : d89460 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89196, d89460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89196, d89460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10817 (p : Pattern) (ha : d89202 p = 1) (hb : d89466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89197 q = 1) (hb : d89461 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89197, d89461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89197, d89461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10816 q ha hb
  have h2 (q : Pattern) (ha : d89198 q = 1) (hb : d89462 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89198, d89462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89198, d89462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89199 q = 1) (hb : d89463 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89199, d89463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89199, d89463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89200 q = 1) (hb : d89464 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89200, d89464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89200, d89464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89201 q = 1) (hb : d89465 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89201, d89465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89201, d89465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89202 q = 1) (hb : d89466 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89202, d89466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89202, d89466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10818 (p : Pattern) (ha : d88761 p = 1) (hb : d89474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d86583 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d86594 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88757 q = 1) (hb : d89470 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88757, d89470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88757, d89470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d86622 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d88758 q = 1) (hb : d89471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88758, d89471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88758, d89471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88759 q = 1) (hb : d89472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88759, d89472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88759, d89472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88760 q = 1) (hb : d89473 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88760, d89473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88760, d89473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88761 q = 1) (hb : d89474 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88761, d89474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88761, d89474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10819 (p : Pattern) (ha : d88770 p = 1) (hb : d89479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d86574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86583 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d86594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88757 q = 1) (hb : d89470 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88757, d89470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88757, d89470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d86622 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88758 q = 1) (hb : d89471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88758, d89471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88758, d89471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88759 q = 1) (hb : d89472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88759, d89472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88759, d89472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88760 q = 1) (hb : d89473 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88760, d89473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88760, d89473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d86632 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d86637 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d86639 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88765 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88766 q = 1) (hb : d89475 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88766, d89475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88766, d89475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d86646 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d88767 q = 1) (hb : d89476 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88767, d89476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88767, d89476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88768 q = 1) (hb : d89477 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88768, d89477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88768, d89477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88769 q = 1) (hb : d89478 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88769, d89478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88769, d89478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d88770 q = 1) (hb : d89479 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88770, d89479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88770, d89479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10820 (p : Pattern) (ha : d89208 p = 1) (hb : d89486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86639 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88765 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88766 q = 1) (hb : d89475 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88766, d89475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88766, d89475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d86646 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88767 q = 1) (hb : d89476 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88767, d89476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88767, d89476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88768 q = 1) (hb : d89484 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88768, d89484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88768, d89484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88769 q = 1) (hb : d89485 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88769, d89485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88769, d89485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89208 q = 1) (hb : d89486 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89208, d89486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89208, d89486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10821 (p : Pattern) (ha : d89218 p = 1) (hb : d89496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88880 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d89214 q = 1) (hb : d89492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89214, d89492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89214, d89492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d86732 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89215 q = 1) (hb : d89493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89215, d89493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89215, d89493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89216 q = 1) (hb : d89494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89216, d89494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89216, d89494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89217 q = 1) (hb : d89495 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89217, d89495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89217, d89495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89218 q = 1) (hb : d89496 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89218, d89496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89218, d89496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10822 (p : Pattern) (ha : d89224 p = 1) (hb : d89502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d86566 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88771 q = 1) (hb : d89480 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88771, d89480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10818 q ha hb
    | true =>
      simp only [d88771, d89480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10819 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d86664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88772 q = 1) (hb : d89481 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88772, d89481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88772, d89481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89206 q = 1) (hb : d89482 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89206, d89482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89206, d89482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89207 q = 1) (hb : d89483 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89207, d89483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89207, d89483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89209 q = 1) (hb : d89487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89209, d89487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89209, d89487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10820 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d86673 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d89210 q = 1) (hb : d89488 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89210, d89488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89210, d89488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d89211 q = 1) (hb : d89489 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89211, d89489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89211, d89489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89212 q = 1) (hb : d89490 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89212, d89490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d89212, d89490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d89213 q = 1) (hb : d89491 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89213, d89491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89213, d89491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d89219 q = 1) (hb : d89497 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89219, d89497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89219, d89497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10821 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d86748 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d89220 q = 1) (hb : d89498 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89220, d89498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89220, d89498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d89221 q = 1) (hb : d89499 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89221, d89499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89221, d89499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89222 q = 1) (hb : d89500 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89222, d89500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d89222, d89500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d89223 q = 1) (hb : d89501 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89223, d89501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d89223, d89501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d89224 q = 1) (hb : d89502 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89224, d89502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89224, d89502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10823 (p : Pattern) (ha : d89230 p = 1) (hb : d89508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89225 q = 1) (hb : d89503 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89225, d89503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89225, d89503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10822 q ha hb
  have h2 (q : Pattern) (ha : d89226 q = 1) (hb : d89504 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89226, d89504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89226, d89504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89227 q = 1) (hb : d89505 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89227, d89505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89227, d89505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89228 q = 1) (hb : d89506 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89228, d89506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89228, d89506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89229 q = 1) (hb : d89507 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89229, d89507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89229, d89507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89230 q = 1) (hb : d89508 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89230, d89508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89230, d89508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10824 (p : Pattern) (ha : d88915 p = 1) (hb : d89517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d86819 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d86830 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88911 q = 1) (hb : d89513 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88911, d89513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88911, d89513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d86858 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d88912 q = 1) (hb : d89514 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88912, d89514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88912, d89514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88913 q = 1) (hb : d89515 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88913, d89515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88913, d89515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88914 q = 1) (hb : d89516 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88914, d89516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88914, d89516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88915 q = 1) (hb : d89517 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88915, d89517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88915, d89517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10825 (p : Pattern) (ha : d88924 p = 1) (hb : d89522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d86810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86819 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d86830 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88911 q = 1) (hb : d89513 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88911, d89513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88911, d89513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d86858 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88912 q = 1) (hb : d89514 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88912, d89514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88912, d89514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88913 q = 1) (hb : d89515 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88913, d89515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88913, d89515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88914 q = 1) (hb : d89516 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88914, d89516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88914, d89516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d86868 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d86873 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d86875 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88919 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88920 q = 1) (hb : d89518 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88920, d89518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88920, d89518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d86882 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d88921 q = 1) (hb : d89519 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88921, d89519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88921, d89519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88922 q = 1) (hb : d89520 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88922, d89520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88922, d89520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88923 q = 1) (hb : d89521 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88923, d89521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88923, d89521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d88924 q = 1) (hb : d89522 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88924, d89522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88924, d89522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10826 (p : Pattern) (ha : d89237 p = 1) (hb : d89529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86875 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88919 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88920 q = 1) (hb : d89518 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88920, d89518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88920, d89518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d86882 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88921 q = 1) (hb : d89519 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88921, d89519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88921, d89519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88922 q = 1) (hb : d89527 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88922, d89527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88922, d89527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88923 q = 1) (hb : d89528 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88923, d89528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88923, d89528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89237 q = 1) (hb : d89529 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89237, d89529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89237, d89529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10827 (p : Pattern) (ha : d89247 p = 1) (hb : d89539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d86940 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d89034 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d89243 q = 1) (hb : d89535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89243, d89535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89243, d89535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d86968 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89244 q = 1) (hb : d89536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89244, d89536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89244, d89536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89245 q = 1) (hb : d89537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89245, d89537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89245, d89537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89246 q = 1) (hb : d89538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89246, d89538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89246, d89538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89247 q = 1) (hb : d89539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89247, d89539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89247, d89539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10828 (p : Pattern) (ha : d89253 p = 1) (hb : d89545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d86802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88925 q = 1) (hb : d89523 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88925, d89523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10824 q ha hb
    | true =>
      simp only [d88925, d89523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10825 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d86900 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88926 q = 1) (hb : d89524 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88926, d89524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88926, d89524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89235 q = 1) (hb : d89525 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89235, d89525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89235, d89525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89236 q = 1) (hb : d89526 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89236, d89526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89236, d89526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89238 q = 1) (hb : d89530 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89238, d89530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89238, d89530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10826 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d86909 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d89239 q = 1) (hb : d89531 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89239, d89531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89239, d89531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d89240 q = 1) (hb : d89532 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89240, d89532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89240, d89532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89241 q = 1) (hb : d89533 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89241, d89533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d89241, d89533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d89242 q = 1) (hb : d89534 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89242, d89534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89242, d89534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d89248 q = 1) (hb : d89540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89248, d89540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89248, d89540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10827 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d86984 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d89249 q = 1) (hb : d89541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89249, d89541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89249, d89541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d89250 q = 1) (hb : d89542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89250, d89542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89250, d89542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89251 q = 1) (hb : d89543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89251, d89543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d89251, d89543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d89252 q = 1) (hb : d89544 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89252, d89544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d89252, d89544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d89253 q = 1) (hb : d89545 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89253, d89545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89253, d89545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10829 (p : Pattern) (ha : d89259 p = 1) (hb : d89551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89254 q = 1) (hb : d89546 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89254, d89546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89254, d89546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10828 q ha hb
  have h2 (q : Pattern) (ha : d89255 q = 1) (hb : d89547 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89255, d89547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89255, d89547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89256 q = 1) (hb : d89548 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89256, d89548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89256, d89548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89257 q = 1) (hb : d89549 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89257, d89549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89257, d89549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89258 q = 1) (hb : d89550 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89258, d89550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89258, d89550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89259 q = 1) (hb : d89551 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89259, d89551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89259, d89551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10830 (p : Pattern) (ha : d89265 p = 1) (hb : d89557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d89150 q = 1) (hb : d89386 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89150, d89386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10799 q ha hb
    | true =>
      simp only [d89150, d89386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10805 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d89176 q = 1) (hb : d89426 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89176, d89426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89176, d89426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10811 q ha hb
  have h3 (q : Pattern) (ha : d89177 q = 1) (hb : d89427 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d89177, d89427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89177, d89427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89203 q = 1) (hb : d89467 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89203, d89467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89203, d89467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10817 q ha hb
  have h5 (q : Pattern) (ha : d89204 q = 1) (hb : d89468 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d89204, d89468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89204, d89468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89205 q = 1) (hb : d89469 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d89205, d89469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89205, d89469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89231 q = 1) (hb : d89509 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89231, d89509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89231, d89509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10823 q ha hb
  have h8 (q : Pattern) (ha : d89232 q = 1) (hb : d89510 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d89232, d89510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89232, d89510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d89233 q = 1) (hb : d89511 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d89233, d89511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89233, d89511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d89234 q = 1) (hb : d89512 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d89234, d89512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89234, d89512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d89260 q = 1) (hb : d89552 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89260, d89552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89260, d89552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10829 q ha hb
  have h12 (q : Pattern) (ha : d89261 q = 1) (hb : d89553 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d89261, d89553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89261, d89553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d89262 q = 1) (hb : d89554 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d89262, d89554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89262, d89554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d89263 q = 1) (hb : d89555 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d89263, d89555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89263, d89555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d89264 q = 1) (hb : d89556 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d89264, d89556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d89264, d89556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d89265 q = 1) (hb : d89557 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d89265, d89557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89265, d89557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro10831 (p : Pattern) (ha : d89271 p = 1) (hb : d89563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89266 q = 1) (hb : d89558 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d89266, d89558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10830 q ha hb
    | true =>
      simp only [d89266, d89558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89267 q = 1) (hb : d89559 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d89267, d89559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89267, d89559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89268 q = 1) (hb : d89560 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d89268, d89560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89268, d89560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89269 q = 1) (hb : d89561 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d89269, d89561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89269, d89561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89270 q = 1) (hb : d89562 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d89270, d89562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89270, d89562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89271 q = 1) (hb : d89563 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d89271, d89563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89271, d89563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10832 (p : Pattern) (ha : d89277 p = 1) (hb : d89569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89272 q = 1) (hb : d89564 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d89272, d89564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10831 q ha hb
    | true =>
      simp only [d89272, d89564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89273 q = 1) (hb : d89565 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d89273, d89565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89273, d89565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89274 q = 1) (hb : d89566 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d89274, d89566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89274, d89566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89275 q = 1) (hb : d89567 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d89275, d89567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89275, d89567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89276 q = 1) (hb : d89568 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d89276, d89568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89276, d89568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89277 q = 1) (hb : d89569 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d89277, d89569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89277, d89569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10833 (p : Pattern) (ha : d89283 p = 1) (hb : d89575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89278 q = 1) (hb : d89570 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d89278, d89570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10832 q ha hb
    | true =>
      simp only [d89278, d89570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89279 q = 1) (hb : d89571 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d89279, d89571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89279, d89571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89280 q = 1) (hb : d89572 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d89280, d89572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89280, d89572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89281 q = 1) (hb : d89573 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d89281, d89573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89281, d89573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89282 q = 1) (hb : d89574 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d89282, d89574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89282, d89574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89283 q = 1) (hb : d89575 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d89283, d89575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89283, d89575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10834 (p : Pattern) (ha : d89289 p = 1) (hb : d89581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89284 q = 1) (hb : d89576 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d89284, d89576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10833 q ha hb
    | true =>
      simp only [d89284, d89576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89285 q = 1) (hb : d89577 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d89285, d89577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89285, d89577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89286 q = 1) (hb : d89578 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d89286, d89578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89286, d89578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89287 q = 1) (hb : d89579 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d89287, d89579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89287, d89579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89288 q = 1) (hb : d89580 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d89288, d89580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89288, d89580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89289 q = 1) (hb : d89581 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d89289, d89581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89289, d89581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10835 (p : Pattern) (ha : d89295 p = 1) (hb : d89587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89290 q = 1) (hb : d89582 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d89290, d89582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10834 q ha hb
    | true =>
      simp only [d89290, d89582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89291 q = 1) (hb : d89583 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d89291, d89583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89291, d89583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89292 q = 1) (hb : d89584 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d89292, d89584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89292, d89584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89293 q = 1) (hb : d89585 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d89293, d89585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89293, d89585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89294 q = 1) (hb : d89586 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d89294, d89586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89294, d89586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89295 q = 1) (hb : d89587 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d89295, d89587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89295, d89587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10836 (p : Pattern) (ha : d89301 p = 1) (hb : d89593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89296 q = 1) (hb : d89588 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d89296, d89588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10835 q ha hb
    | true =>
      simp only [d89296, d89588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89297 q = 1) (hb : d89589 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d89297, d89589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89297, d89589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89298 q = 1) (hb : d89590 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d89298, d89590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89298, d89590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89299 q = 1) (hb : d89591 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d89299, d89591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89299, d89591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89300 q = 1) (hb : d89592 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d89300, d89592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89300, d89592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89301 q = 1) (hb : d89593 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d89301, d89593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89301, d89593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10837 (p : Pattern) (ha : d89307 p = 1) (hb : d89599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89302 q = 1) (hb : d89594 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d89302, d89594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10836 q ha hb
    | true =>
      simp only [d89302, d89594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89303 q = 1) (hb : d89595 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d89303, d89595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89303, d89595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89304 q = 1) (hb : d89596 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d89304, d89596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89304, d89596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89305 q = 1) (hb : d89597 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d89305, d89597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89305, d89597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89306 q = 1) (hb : d89598 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d89306, d89598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89306, d89598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89307 q = 1) (hb : d89599 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d89307, d89599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89307, d89599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10838 (p : Pattern) (ha : d77112 p = 1) (hb : d89600 p = 1) : d77112 p = 1 := by
  have h0 (q : Pattern) (ha : d77112 q = 1) (hb : d89600 q = 1) : d77112 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro10839 (p : Pattern) (ha : d52013 p = 1) (hb : d76787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5850 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52009 q = 1) (hb : d76783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52009, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52009, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d52010 q = 1) (hb : d76784 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52010, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d52011 q = 1) (hb : d76785 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d52011, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52012 q = 1) (hb : d76786 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52012, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52013 q = 1) (hb : d76787 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52013, d76787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52013, d76787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro10840 (p : Pattern) (ha : d52029 p = 1) (hb : d76792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5850 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52009 q = 1) (hb : d76783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52009, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52009, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d52010 q = 1) (hb : d76784 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52010, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d52011 q = 1) (hb : d76785 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d52011, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52012 q = 1) (hb : d76786 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52012, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d5856 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
    | true =>
      simp only [d5856, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52025 q = 1) (hb : d76788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52025, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52025, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d52026 q = 1) (hb : d76789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d52026, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d52027 q = 1) (hb : d76790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52027, d76790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d52027, d76790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d52028 q = 1) (hb : d76791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52028, d76791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d52028, d76791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d52029 q = 1) (hb : d76792 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52029, d76792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52029, d76792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro10841 (p : Pattern) (ha : d52038 p = 1) (hb : d76799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5856 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
    | true =>
      simp only [d5856, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52025 q = 1) (hb : d76788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52025, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52025, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52026 q = 1) (hb : d76789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52026, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52036 q = 1) (hb : d76797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52036, d76797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52036, d76797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52037 q = 1) (hb : d76798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52037, d76798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52037, d76798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52038 q = 1) (hb : d76799 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52038, d76799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52038, d76799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10842 (p : Pattern) (ha : d52067 p = 1) (hb : d76809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5874 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5874, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8906 q ha hb
    | true =>
      simp only [d5874, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52063 q = 1) (hb : d76805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52063, d76805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52063, d76805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52064 q = 1) (hb : d76806 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52064, d76806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52064, d76806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52065 q = 1) (hb : d76807 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52065, d76807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52065, d76807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52066 q = 1) (hb : d76808 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52066, d76808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52066, d76808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52067 q = 1) (hb : d76809 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52067, d76809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52067, d76809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10843 (p : Pattern) (ha : d52073 p = 1) (hb : d76815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d51957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52030 q = 1) (hb : d76793 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d76793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10839 q ha hb
    | true =>
      simp only [d52030, d76793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10840 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52033 q = 1) (hb : d76794 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d76794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52033, d76794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52034 q = 1) (hb : d76795 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d76795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52034, d76795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52035 q = 1) (hb : d76796 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d76796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d76796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52039 q = 1) (hb : d76800 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52039, d76800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52039, d76800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10841 q ha hb
  have h12 (q : Pattern) (ha : d52040 q = 1) (hb : d76801 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52040, d76801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52040, d76801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d52041 q = 1) (hb : d76802 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52041, d76802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52041, d76802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d52042 q = 1) (hb : d76803 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52042, d76803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52042, d76803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d52043 q = 1) (hb : d76804 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d76804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52043, d76804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52068 q = 1) (hb : d76810 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52068, d76810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52068, d76810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10842 q ha hb
  have h17 (q : Pattern) (ha : d52069 q = 1) (hb : d76811 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52069, d76811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52069, d76811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d52070 q = 1) (hb : d76812 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52070, d76812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52070, d76812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d52071 q = 1) (hb : d76813 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52071, d76813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d52071, d76813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d52072 q = 1) (hb : d76814 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52072, d76814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d52072, d76814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d52073 q = 1) (hb : d76815 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52073, d76815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52073, d76815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro10844 (p : Pattern) (ha : d5895 p = 1) (hb : d52083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5850 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d5891 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5892 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5892, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5893 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5894 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5895 q = 1) (hb : d52083 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5895, d52083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5895, d52083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10845 (p : Pattern) (ha : d5902 p = 1) (hb : d52090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5850 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d5891 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5892 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5892, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5893 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5894 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5856 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
    | true =>
      simp only [d5856, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h7 (q : Pattern) (ha : d5898 q = 1) (hb : d52086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d52086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5898, d52086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5899 q = 1) (hb : d52087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, d52087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5899, d52087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5900 q = 1) (hb : d52088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, d52088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5900, d52088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5901 q = 1) (hb : d52089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, d52089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5901, d52089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5902 q = 1) (hb : d52090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5902, d52090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5902, d52090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10846 (p : Pattern) (ha : d5952 p = 1) (hb : d52163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5850 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d5891 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5892 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5892, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5893 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5894 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d51952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d51953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d51954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5952 q = 1) (hb : d52163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5952, d52163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5952, d52163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10847 (p : Pattern) (ha : d76825 p = 1) (hb : d81539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5908 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5908, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8916 q ha hb
    | true =>
      simp only [d5908, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d5909 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5909, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5909, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5910 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5910, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5910, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5911 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5911, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5911, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5915 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5915, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8917 q ha hb
    | true =>
      simp only [d5915, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d5916 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5916, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5916, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5917 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5917, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5917, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5922 q = 1) (hb : d81534 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5922, d81534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8918 q ha hb
    | true =>
      simp only [d5922, d81534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76821 q = 1) (hb : d81535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76821, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76821, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4737 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d4737, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5350 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5350, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76822 q = 1) (hb : d81536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76822, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76822, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76823 q = 1) (hb : d81537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76823, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76823, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76824 q = 1) (hb : d81538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76824, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76824, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76825 q = 1) (hb : d81539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76825, d81539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76825, d81539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro10848 (p : Pattern) (ha : d76830 p = 1) (hb : d81546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5908 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5908, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8916 q ha hb
    | true =>
      simp only [d5908, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d5909 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5909, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5909, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5910 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5910, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5910, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5911 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5911, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5911, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5915 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5915, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8917 q ha hb
    | true =>
      simp only [d5915, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d5916 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5916, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5916, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5917 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5917, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5917, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5922 q = 1) (hb : d81534 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5922, d81534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8918 q ha hb
    | true =>
      simp only [d5922, d81534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76821 q = 1) (hb : d81535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76821, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76821, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4737 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d4737, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5350 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5350, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76822 q = 1) (hb : d81536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76822, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76822, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76823 q = 1) (hb : d81537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76823, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76823, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76824 q = 1) (hb : d81538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76824, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76824, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5934 q = 1) (hb : d52145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5934, d52145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8920 q ha hb
    | true =>
      simp only [d5934, d52145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
  have h17 (q : Pattern) (ha : d5935 q = 1) (hb : d52146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5935, d52146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5935, d52146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d5936 q = 1) (hb : d52147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5936, d52147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5936, d52147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d5937 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5937, d52148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5937, d52148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d5939 q = 1) (hb : d52150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5939, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8921 q ha hb
    | true =>
      simp only [d5939, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h21 (q : Pattern) (ha : d5940 q = 1) (hb : d52151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5940, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5940, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d5941 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5941, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d5941, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d5943 q = 1) (hb : d81541 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5943, d81541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8912 q ha hb
    | true =>
      simp only [d5943, d81541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d76826 q = 1) (hb : d81542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76826, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76826, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d5356 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d5357 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d5357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d76827 q = 1) (hb : d81543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76827, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d76828 q = 1) (hb : d81544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76828, d81544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76828, d81544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d76829 q = 1) (hb : d81545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76829, d81545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76829, d81545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76830 q = 1) (hb : d81546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76830, d81546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76830, d81546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro10849 (p : Pattern) (ha : d76837 p = 1) (hb : d81553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5943 q = 1) (hb : d81541 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5943, d81541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8912 q ha hb
    | true =>
      simp only [d5943, d81541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76826 q = 1) (hb : d81542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76826, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76826, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5356 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5357 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76827 q = 1) (hb : d81543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76827, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76835 q = 1) (hb : d81551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76835, d81551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76835, d81551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76836 q = 1) (hb : d81552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76836, d81552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76836, d81552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76837 q = 1) (hb : d81553 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76837, d81553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76837, d81553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10850 (p : Pattern) (ha : d76847 p = 1) (hb : d81572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5969 q = 1) (hb : d81567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5969, d81567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8914 q ha hb
    | true =>
      simp only [d5969, d81567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8906 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76843 q = 1) (hb : d81568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76843, d81568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76843, d81568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5378 q = 1) (hb : d74104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7498 q ha hb
    | true =>
      simp only [d5378, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5379 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5379, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76844 q = 1) (hb : d81569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76844, d81569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76844, d81569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76845 q = 1) (hb : d81570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76845, d81570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76845, d81570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76846 q = 1) (hb : d81571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76846, d81571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76846, d81571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76847 q = 1) (hb : d81572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76847, d81572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76847, d81572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10851 (p : Pattern) (ha : d76853 p = 1) (hb : d81578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5896 q = 1) (hb : d52084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5896, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5896, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10844 q ha hb
  have h2 (q : Pattern) (ha : d5897 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5897, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5897, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5903 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5903, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10844 q ha hb
    | true =>
      simp only [d5903, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10845 q ha hb
  have h4 (q : Pattern) (ha : d5904 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5904, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5904, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5905 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d5905, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5905, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76831 q = 1) (hb : d81547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76831, d81547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10847 q ha hb
    | true =>
      simp only [d76831, d81547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10848 q ha hb
  have h7 (q : Pattern) (ha : d5953 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5953, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10846 q ha hb
    | true =>
      simp only [d5953, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h8 (q : Pattern) (ha : d76832 q = 1) (hb : d81548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76832, d81548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76832, d81548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76833 q = 1) (hb : d81549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76833, d81549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76833, d81549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d76834 q = 1) (hb : d81550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76834, d81550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76834, d81550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76838 q = 1) (hb : d81554 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76838, d81554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76838, d81554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10849 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39 q ha hb
  have h13 (q : Pattern) (ha : d76839 q = 1) (hb : d81555 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76839, d81555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76839, d81555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76840 q = 1) (hb : d81556 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76840, d81556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76840, d81556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d76841 q = 1) (hb : d81557 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76841, d81557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76841, d81557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76842 q = 1) (hb : d81558 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76842, d81558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76842, d81558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76848 q = 1) (hb : d81573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76848, d81573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76848, d81573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10850 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40 q ha hb
  have h19 (q : Pattern) (ha : d76849 q = 1) (hb : d81574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76849, d81574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76849, d81574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76850 q = 1) (hb : d81575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76850, d81575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76850, d81575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d76851 q = 1) (hb : d81576 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76851, d81576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76851, d81576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76852 q = 1) (hb : d81577 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76852, d81577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76852, d81577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76853 q = 1) (hb : d81578 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76853, d81578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76853, d81578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro10852 (p : Pattern) (ha : d76859 p = 1) (hb : d81584 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d52074 q = 1) (hb : d76816 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d76816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52074, d76816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10843 q ha hb
  have h6 (q : Pattern) (ha : d52075 q = 1) (hb : d76817 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d76817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52075, d76817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52076 q = 1) (hb : d76818 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d76818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52076, d76818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52077 q = 1) (hb : d76819 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d76819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52077, d76819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52078 q = 1) (hb : d76820 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d76820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52078, d76820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76854 q = 1) (hb : d81579 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76854, d81579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76854, d81579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10851 q ha hb
  have h11 (q : Pattern) (ha : d76855 q = 1) (hb : d81580 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76855, d81580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76855, d81580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76856 q = 1) (hb : d81581 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76856, d81581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76856, d81581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76857 q = 1) (hb : d81582 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76857, d81582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76857, d81582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76858 q = 1) (hb : d81583 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76858, d81583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76858, d81583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76859 q = 1) (hb : d81584 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76859, d81584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76859, d81584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10853 (p : Pattern) (ha : d5997 p = 1) (hb : d52244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5992 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5992, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8927 q ha hb
    | true =>
      simp only [d5992, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d5993 q = 1) (hb : d52240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5993, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5994 q = 1) (hb : d52241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5994, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5995 q = 1) (hb : d52242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5995, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5996 q = 1) (hb : d52243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5997 q = 1) (hb : d52244 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5997, d52244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5997, d52244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10854 (p : Pattern) (ha : d6005 p = 1) (hb : d52254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5992 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5992, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8927 q ha hb
    | true =>
      simp only [d5992, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d5993 q = 1) (hb : d52240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5993, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5994 q = 1) (hb : d52241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5994, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5995 q = 1) (hb : d52242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5995, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5996 q = 1) (hb : d52243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6000 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6000, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8929 q ha hb
    | true =>
      simp only [d6000, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h7 (q : Pattern) (ha : d6001 q = 1) (hb : d52250 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d52250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6001, d52250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6002 q = 1) (hb : d52251 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, d52251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6002, d52251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6003 q = 1) (hb : d52252 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, d52252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6003, d52252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6004 q = 1) (hb : d52253 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, d52253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6004, d52253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6005 q = 1) (hb : d52254 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6005, d52254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6005, d52254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10855 (p : Pattern) (ha : d6061 p = 1) (hb : d81618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6056 q = 1) (hb : d81613 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6056, d81613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8925 q ha hb
    | true =>
      simp only [d6056, d81613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d6057 q = 1) (hb : d81614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6057, d81614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6057, d81614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6058 q = 1) (hb : d81615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6058, d81615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6058, d81615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6059 q = 1) (hb : d81616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6059, d81616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6059, d81616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6060 q = 1) (hb : d81617 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6060, d81617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6060, d81617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
    | true =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6061 q = 1) (hb : d81618 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6061, d81618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6061, d81618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10856 (p : Pattern) (ha : d76864 p = 1) (hb : d81603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6011 q = 1) (hb : d52262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6011, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8935 q ha hb
    | true =>
      simp only [d6011, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q ha hb
  have h2 (q : Pattern) (ha : d6012 q = 1) (hb : d52263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6012, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6012, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6013 q = 1) (hb : d52264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6013, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6013, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6014 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6014, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6014, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6018 q = 1) (hb : d52272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6018, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8936 q ha hb
    | true =>
      simp only [d6018, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h6 (q : Pattern) (ha : d6019 q = 1) (hb : d52273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6019, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6019, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6020 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6020, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6020, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6025 q = 1) (hb : d81598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6025, d81598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8937 q ha hb
    | true =>
      simp only [d6025, d81598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8925 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76860 q = 1) (hb : d81599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76860, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76860, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5400 q = 1) (hb : d74126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7510 q ha hb
    | true =>
      simp only [d5400, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5401 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5401, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76861 q = 1) (hb : d81600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76861, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76862 q = 1) (hb : d81601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76862, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76863 q = 1) (hb : d81602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76863, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76864 q = 1) (hb : d81603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76864, d81603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76864, d81603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro10857 (p : Pattern) (ha : d6046 p = 1) (hb : d81605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4825 q = 1) (hb : d68921 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4825, d68921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7918 q ha hb
    | true =>
      simp only [d4825, d68921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4826 q = 1) (hb : d68922 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4826, d68922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4826, d68922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4827 q = 1) (hb : d81594 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4827, d81594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4827, d81594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4828 q = 1) (hb : d81595 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4828, d81595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4828, d81595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4829 q = 1) (hb : d81596 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4829, d81596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4829, d81596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6046 q = 1) (hb : d81605 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6046, d81605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6046, d81605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro10858 (p : Pattern) (ha : d76869 p = 1) (hb : d81611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6011 q = 1) (hb : d52262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6011, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8935 q ha hb
    | true =>
      simp only [d6011, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q ha hb
  have h2 (q : Pattern) (ha : d6012 q = 1) (hb : d52263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6012, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6012, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6013 q = 1) (hb : d52264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6013, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6013, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6014 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6014, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6014, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6018 q = 1) (hb : d52272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6018, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8936 q ha hb
    | true =>
      simp only [d6018, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h6 (q : Pattern) (ha : d6019 q = 1) (hb : d52273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6019, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6019, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6020 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6020, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6020, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6025 q = 1) (hb : d81598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6025, d81598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8937 q ha hb
    | true =>
      simp only [d6025, d81598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8925 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76860 q = 1) (hb : d81599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76860, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76860, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5400 q = 1) (hb : d74126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7510 q ha hb
    | true =>
      simp only [d5400, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5401 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5401, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76861 q = 1) (hb : d81600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76861, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76862 q = 1) (hb : d81601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76862, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76863 q = 1) (hb : d81602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76863, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6037 q = 1) (hb : d52318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6037, d52318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8939 q ha hb
    | true =>
      simp only [d6037, d52318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94 q ha hb
  have h17 (q : Pattern) (ha : d6038 q = 1) (hb : d52319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6038, d52319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6038, d52319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6039 q = 1) (hb : d52320 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6039, d52320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d6039, d52320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d6040 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6040, d52321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6040, d52321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6042 q = 1) (hb : d52324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6042, d52324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8940 q ha hb
    | true =>
      simp only [d6042, d52324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96 q ha hb
  have h21 (q : Pattern) (ha : d6043 q = 1) (hb : d52325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6043, d52325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6043, d52325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d6044 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6044, d52326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d6044, d52326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d6047 q = 1) (hb : d81606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6047, d81606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8931 q ha hb
    | true =>
      simp only [d6047, d81606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10857 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d76865 q = 1) (hb : d81607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76865, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76865, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d5407 q = 1) (hb : d74133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7513 q ha hb
    | true =>
      simp only [d5407, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d5408 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d5408, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d76866 q = 1) (hb : d81608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76866, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d76867 q = 1) (hb : d81609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76867, d81609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76867, d81609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d76868 q = 1) (hb : d81610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76868, d81610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76868, d81610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76869 q = 1) (hb : d81611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76869, d81611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76869, d81611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro10859 (p : Pattern) (ha : d76876 p = 1) (hb : d81625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6047 q = 1) (hb : d81606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6047, d81606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8931 q ha hb
    | true =>
      simp only [d6047, d81606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10857 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76865 q = 1) (hb : d81607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76865, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76865, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5407 q = 1) (hb : d74133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7513 q ha hb
    | true =>
      simp only [d5407, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5408 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5408, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76866 q = 1) (hb : d81608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76866, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76874 q = 1) (hb : d81623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76874, d81623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76874, d81623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76875 q = 1) (hb : d81624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76875, d81624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76875, d81624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76876 q = 1) (hb : d81625 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76876, d81625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76876, d81625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10860 (p : Pattern) (ha : d6078 p = 1) (hb : d75840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d230 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6078 q = 1) (hb : d75840 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6078, d75840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6078, d75840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro10861 (p : Pattern) (ha : d6084 p = 1) (hb : d75846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d421 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d421, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6079 q = 1) (hb : d75841 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q ha hb
    | true =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h9 (q : Pattern) (ha : d6080 q = 1) (hb : d75842 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6081 q = 1) (hb : d75843 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6082 q = 1) (hb : d75844 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d75844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6082, d75844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6083 q = 1) (hb : d75845 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6083, d75845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6083, d75845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6084 q = 1) (hb : d75846 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6084, d75846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6084, d75846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro10862 (p : Pattern) (ha : d6090 p = 1) (hb : d81643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6085 q = 1) (hb : d75847 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6085, d75847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10861 q ha hb
    | true =>
      simp only [d6085, d75847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6086 q = 1) (hb : d75848 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6086, d75848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6086, d75848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6087 q = 1) (hb : d81640 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6087, d81640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6087, d81640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6088 q = 1) (hb : d81641 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6088, d81641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6088, d81641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6089 q = 1) (hb : d81642 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6089, d81642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6089, d81642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6090 q = 1) (hb : d81643 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6090, d81643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6090, d81643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro10863 (p : Pattern) (ha : d76886 p = 1) (hb : d81649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6091 q = 1) (hb : d81644 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6091, d81644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8933 q ha hb
    | true =>
      simp only [d6091, d81644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10862 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52399 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76882 q = 1) (hb : d81645 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76882, d81645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76882, d81645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5429 q = 1) (hb : d74155 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5429, d74155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7517 q ha hb
    | true =>
      simp only [d5429, d74155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5430 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5430, d74156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5430, d74156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76883 q = 1) (hb : d81646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76883, d81646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76883, d81646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76884 q = 1) (hb : d81647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76884, d81647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76884, d81647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76885 q = 1) (hb : d81648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76885, d81648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76885, d81648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76886 q = 1) (hb : d81649 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76886, d81649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76886, d81649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10864 (p : Pattern) (ha : d76892 p = 1) (hb : d81655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5998 q = 1) (hb : d52245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5998, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5998, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10853 q ha hb
  have h2 (q : Pattern) (ha : d5999 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5999, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5999, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6006 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6006, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10853 q ha hb
    | true =>
      simp only [d6006, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10854 q ha hb
  have h4 (q : Pattern) (ha : d6007 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6007, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6007, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6008 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6008, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6008, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76870 q = 1) (hb : d81612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76870, d81612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10856 q ha hb
    | true =>
      simp only [d76870, d81612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10858 q ha hb
  have h7 (q : Pattern) (ha : d6062 q = 1) (hb : d81619 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6062, d81619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10855 q ha hb
    | true =>
      simp only [d6062, d81619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69 q ha hb
  have h8 (q : Pattern) (ha : d76871 q = 1) (hb : d81620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76871, d81620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76871, d81620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76872 q = 1) (hb : d81621 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76872, d81621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76872, d81621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d76873 q = 1) (hb : d81622 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76873, d81622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76873, d81622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76877 q = 1) (hb : d81626 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76877, d81626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76877, d81626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10859 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70 q ha hb
  have h13 (q : Pattern) (ha : d76878 q = 1) (hb : d81627 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76878, d81627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76878, d81627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76879 q = 1) (hb : d81628 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76879, d81628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76879, d81628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d76880 q = 1) (hb : d81629 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76880, d81629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76880, d81629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76881 q = 1) (hb : d81630 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76881, d81630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76881, d81630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76887 q = 1) (hb : d81650 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76887, d81650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76887, d81650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10863 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73 q ha hb
  have h19 (q : Pattern) (ha : d76888 q = 1) (hb : d81651 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76888, d81651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76888, d81651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76889 q = 1) (hb : d81652 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76889, d81652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76889, d81652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d76890 q = 1) (hb : d81653 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76890, d81653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76890, d81653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76891 q = 1) (hb : d81654 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76891, d81654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76891, d81654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76892 q = 1) (hb : d81655 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76892, d81655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76892, d81655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro10865 (p : Pattern) (ha : d76898 p = 1) (hb : d81661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76893 q = 1) (hb : d81656 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76893, d81656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76893, d81656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10864 q ha hb
  have h2 (q : Pattern) (ha : d76894 q = 1) (hb : d81657 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76894, d81657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76894, d81657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76895 q = 1) (hb : d81658 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76895, d81658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76895, d81658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76896 q = 1) (hb : d81659 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76896, d81659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76896, d81659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76897 q = 1) (hb : d81660 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76897, d81660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76897, d81660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76898 q = 1) (hb : d81661 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76898, d81661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76898, d81661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10866 (p : Pattern) (ha : d6124 p = 1) (hb : d52466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6119 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6119, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8946 q ha hb
    | true =>
      simp only [d6119, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d6120 q = 1) (hb : d52462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6120, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6121 q = 1) (hb : d52463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6121, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6122 q = 1) (hb : d52464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6122, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6123 q = 1) (hb : d52465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6124 q = 1) (hb : d52466 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6124, d52466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6124, d52466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10867 (p : Pattern) (ha : d6133 p = 1) (hb : d52476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6119 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6119, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8946 q ha hb
    | true =>
      simp only [d6119, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d6120 q = 1) (hb : d52462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6120, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6121 q = 1) (hb : d52463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6121, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6122 q = 1) (hb : d52464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6122, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6123 q = 1) (hb : d52465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6128 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6128, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8948 q ha hb
    | true =>
      simp only [d6128, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h7 (q : Pattern) (ha : d6129 q = 1) (hb : d52472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d52472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6129, d52472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6130 q = 1) (hb : d52473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, d52473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6130, d52473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6131 q = 1) (hb : d52474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, d52474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6131, d52474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6132 q = 1) (hb : d52475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, d52475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6132, d52475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6133 q = 1) (hb : d52476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6133, d52476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6133, d52476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10868 (p : Pattern) (ha : d6193 p = 1) (hb : d81696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6188 q = 1) (hb : d81691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6188, d81691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8944 q ha hb
    | true =>
      simp only [d6188, d81691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d6189 q = 1) (hb : d81692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6189, d81692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6189, d81692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6190 q = 1) (hb : d81693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6190, d81693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6190, d81693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6191 q = 1) (hb : d81694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6191, d81694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6191, d81694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6192 q = 1) (hb : d81695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6192, d81695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6192, d81695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d52558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
    | true =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d52559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d52560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d52561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6193 q = 1) (hb : d81696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6193, d81696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6193, d81696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10869 (p : Pattern) (ha : d76904 p = 1) (hb : d81681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6139 q = 1) (hb : d52484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6139, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8954 q ha hb
    | true =>
      simp only [d6139, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q ha hb
  have h2 (q : Pattern) (ha : d6140 q = 1) (hb : d52485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6140, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6141 q = 1) (hb : d52486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6141, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6142 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6142, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6146 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6146, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8955 q ha hb
    | true =>
      simp only [d6146, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h6 (q : Pattern) (ha : d6147 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6147, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6148 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6148, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6153 q = 1) (hb : d81676 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, d81676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8956 q ha hb
    | true =>
      simp only [d6153, d81676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8944 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76900 q = 1) (hb : d81677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76900, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76900, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6160 q = 1) (hb : d75913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7522 q ha hb
    | true =>
      simp only [d6160, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6161 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6161, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76901 q = 1) (hb : d81678 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76901, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76902 q = 1) (hb : d81679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76902, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76903 q = 1) (hb : d81680 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76903, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76904 q = 1) (hb : d81681 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76904, d81681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76904, d81681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro10870 (p : Pattern) (ha : d6176 p = 1) (hb : d81683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4920 q = 1) (hb : d69013 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7932 q ha hb
    | true =>
      simp only [d4920, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4921 q = 1) (hb : d69014 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4921, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4922 q = 1) (hb : d81672 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4922, d81672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4922, d81672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4923 q = 1) (hb : d81673 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4923, d81673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4923, d81673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4924 q = 1) (hb : d81674 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4924, d81674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4924, d81674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6176 q = 1) (hb : d81683 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6176, d81683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6176, d81683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro10871 (p : Pattern) (ha : d76909 p = 1) (hb : d81689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6139 q = 1) (hb : d52484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6139, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8954 q ha hb
    | true =>
      simp only [d6139, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q ha hb
  have h2 (q : Pattern) (ha : d6140 q = 1) (hb : d52485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6140, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6141 q = 1) (hb : d52486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6141, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6142 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6142, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6146 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6146, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8955 q ha hb
    | true =>
      simp only [d6146, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h6 (q : Pattern) (ha : d6147 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6147, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6148 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6148, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6153 q = 1) (hb : d81676 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, d81676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8956 q ha hb
    | true =>
      simp only [d6153, d81676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8944 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76900 q = 1) (hb : d81677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76900, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76900, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6160 q = 1) (hb : d75913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7522 q ha hb
    | true =>
      simp only [d6160, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6161 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6161, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76901 q = 1) (hb : d81678 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76901, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76902 q = 1) (hb : d81679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76902, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76903 q = 1) (hb : d81680 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76903, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6167 q = 1) (hb : d52539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6167, d52539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8958 q ha hb
    | true =>
      simp only [d6167, d52539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro141 q ha hb
  have h17 (q : Pattern) (ha : d6168 q = 1) (hb : d52540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6168, d52540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6168, d52540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6169 q = 1) (hb : d52541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6169, d52541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d6169, d52541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d6170 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6170, d52542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6170, d52542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6172 q = 1) (hb : d52545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6172, d52545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8959 q ha hb
    | true =>
      simp only [d6172, d52545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro143 q ha hb
  have h21 (q : Pattern) (ha : d6173 q = 1) (hb : d52546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6173, d52546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6173, d52546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d6174 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6174, d52547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d6174, d52547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d6177 q = 1) (hb : d81684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, d81684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8950 q ha hb
    | true =>
      simp only [d6177, d81684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10870 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d76905 q = 1) (hb : d81685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76905, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76905, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d6181 q = 1) (hb : d75932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7525 q ha hb
    | true =>
      simp only [d6181, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d6182 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d6182, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d76906 q = 1) (hb : d81686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76906, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d76907 q = 1) (hb : d81687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76907, d81687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76907, d81687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d76908 q = 1) (hb : d81688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76908, d81688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76908, d81688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76909 q = 1) (hb : d81689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76909, d81689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76909, d81689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro10872 (p : Pattern) (ha : d76916 p = 1) (hb : d81703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6177 q = 1) (hb : d81684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, d81684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8950 q ha hb
    | true =>
      simp only [d6177, d81684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10870 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76905 q = 1) (hb : d81685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76905, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76905, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6181 q = 1) (hb : d75932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7525 q ha hb
    | true =>
      simp only [d6181, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6182 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6182, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76906 q = 1) (hb : d81686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76906, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76914 q = 1) (hb : d81701 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76914, d81701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76914, d81701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76915 q = 1) (hb : d81702 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76915, d81702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76915, d81702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76916 q = 1) (hb : d81703 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76916, d81703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76916, d81703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10873 (p : Pattern) (ha : d6210 p = 1) (hb : d75961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6210 q = 1) (hb : d75961 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6210, d75961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6210, d75961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro10874 (p : Pattern) (ha : d6216 p = 1) (hb : d75967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d990 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d990, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6211 q = 1) (hb : d75962 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d75962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q ha hb
    | true =>
      simp only [d6211, d75962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h9 (q : Pattern) (ha : d6212 q = 1) (hb : d75963 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d75963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d75963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6213 q = 1) (hb : d75964 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d75964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d75964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6214 q = 1) (hb : d75965 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d75965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6214, d75965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6215 q = 1) (hb : d75966 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6215, d75966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6215, d75966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6216 q = 1) (hb : d75967 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6216, d75967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6216, d75967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro10875 (p : Pattern) (ha : d6222 p = 1) (hb : d81721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6217 q = 1) (hb : d75968 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6217, d75968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10874 q ha hb
    | true =>
      simp only [d6217, d75968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6218 q = 1) (hb : d75969 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6218, d75969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6218, d75969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6219 q = 1) (hb : d81718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6219, d81718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6219, d81718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6220 q = 1) (hb : d81719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6220, d81719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6220, d81719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6221 q = 1) (hb : d81720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6221, d81720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6221, d81720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6222 q = 1) (hb : d81721 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6222, d81721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6222, d81721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro10876 (p : Pattern) (ha : d76926 p = 1) (hb : d81727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6223 q = 1) (hb : d81722 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6223, d81722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8952 q ha hb
    | true =>
      simp only [d6223, d81722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10875 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52636 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76922 q = 1) (hb : d81723 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76922, d81723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76922, d81723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6234 q = 1) (hb : d75981 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6234, d75981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7530 q ha hb
    | true =>
      simp only [d6234, d75981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6235 q = 1) (hb : d75982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6235, d75982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6235, d75982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76923 q = 1) (hb : d81724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76923, d81724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76923, d81724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76924 q = 1) (hb : d81725 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76924, d81725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76924, d81725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76925 q = 1) (hb : d81726 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76925, d81726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76925, d81726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76926 q = 1) (hb : d81727 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76926, d81727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76926, d81727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10877 (p : Pattern) (ha : d76932 p = 1) (hb : d81733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6125 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6125, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6125, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10866 q ha hb
  have h2 (q : Pattern) (ha : d6126 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6126, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6126, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6134 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6134, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10866 q ha hb
    | true =>
      simp only [d6134, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10867 q ha hb
  have h4 (q : Pattern) (ha : d6135 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6135, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6135, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6136 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6136, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6136, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76910 q = 1) (hb : d81690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76910, d81690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10869 q ha hb
    | true =>
      simp only [d76910, d81690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10871 q ha hb
  have h7 (q : Pattern) (ha : d6194 q = 1) (hb : d81697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6194, d81697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10868 q ha hb
    | true =>
      simp only [d6194, d81697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q ha hb
  have h8 (q : Pattern) (ha : d76911 q = 1) (hb : d81698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76911, d81698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76911, d81698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76912 q = 1) (hb : d81699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76912, d81699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76912, d81699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d76913 q = 1) (hb : d81700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76913, d81700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76913, d81700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76917 q = 1) (hb : d81704 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76917, d81704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76917, d81704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10872 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro114 q ha hb
  have h13 (q : Pattern) (ha : d76918 q = 1) (hb : d81705 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76918, d81705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76918, d81705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76919 q = 1) (hb : d81706 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76919, d81706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76919, d81706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d76920 q = 1) (hb : d81707 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76920, d81707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76920, d81707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76921 q = 1) (hb : d81708 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76921, d81708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76921, d81708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76927 q = 1) (hb : d81728 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76927, d81728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76927, d81728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10876 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro119 q ha hb
  have h19 (q : Pattern) (ha : d76928 q = 1) (hb : d81729 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76928, d81729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76928, d81729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76929 q = 1) (hb : d81730 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76929, d81730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76929, d81730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d76930 q = 1) (hb : d81731 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76930, d81731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76930, d81731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76931 q = 1) (hb : d81732 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76931, d81732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76931, d81732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76932 q = 1) (hb : d81733 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76932, d81733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76932, d81733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro10878 (p : Pattern) (ha : d76938 p = 1) (hb : d81739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76933 q = 1) (hb : d81734 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76933, d81734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76933, d81734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10877 q ha hb
  have h2 (q : Pattern) (ha : d76934 q = 1) (hb : d81735 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76934, d81735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76934, d81735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76935 q = 1) (hb : d81736 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76935, d81736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76935, d81736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76936 q = 1) (hb : d81737 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76936, d81737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76936, d81737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76937 q = 1) (hb : d81738 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76937, d81738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76937, d81738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76938 q = 1) (hb : d81739 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76938, d81739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76938, d81739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10879 (p : Pattern) (ha : d6263 p = 1) (hb : d52749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6258 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8965 q ha hb
    | true =>
      simp only [d6258, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d6259 q = 1) (hb : d52745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6259, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6260 q = 1) (hb : d52746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6260, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6261 q = 1) (hb : d52747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6261, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6262 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6263 q = 1) (hb : d52749 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6263, d52749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6263, d52749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10880 (p : Pattern) (ha : d6272 p = 1) (hb : d52759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6258 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8965 q ha hb
    | true =>
      simp only [d6258, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d6259 q = 1) (hb : d52745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6259, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6260 q = 1) (hb : d52746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6260, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6261 q = 1) (hb : d52747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6261, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6262 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6267 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6267, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8967 q ha hb
    | true =>
      simp only [d6267, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h7 (q : Pattern) (ha : d6268 q = 1) (hb : d52755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d52755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6268, d52755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6269 q = 1) (hb : d52756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, d52756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6269, d52756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6270 q = 1) (hb : d52757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, d52757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6270, d52757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6271 q = 1) (hb : d52758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, d52758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6271, d52758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6272 q = 1) (hb : d52759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6272, d52759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6272, d52759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10881 (p : Pattern) (ha : d6332 p = 1) (hb : d81775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6327 q = 1) (hb : d81770 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6327, d81770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8963 q ha hb
    | true =>
      simp only [d6327, d81770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d6328 q = 1) (hb : d81771 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6328, d81771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6328, d81771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6329 q = 1) (hb : d81772 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6329, d81772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6329, d81772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6330 q = 1) (hb : d81773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6330, d81773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6330, d81773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6331 q = 1) (hb : d81774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6331, d81774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6331, d81774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d52838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
    | true =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d52839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d52840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d52841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6332 q = 1) (hb : d81775 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6332, d81775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6332, d81775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10882 (p : Pattern) (ha : d76945 p = 1) (hb : d81760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6278 q = 1) (hb : d52767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6278, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8973 q ha hb
    | true =>
      simp only [d6278, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d6279 q = 1) (hb : d52768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6279, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6280 q = 1) (hb : d52769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6280, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6281 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6281, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6285 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6285, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8974 q ha hb
    | true =>
      simp only [d6285, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d6286 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6286, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6287 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6287, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6292 q = 1) (hb : d81755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, d81755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8975 q ha hb
    | true =>
      simp only [d6292, d81755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8963 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76941 q = 1) (hb : d81756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76941, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76941, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6299 q = 1) (hb : d76041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7534 q ha hb
    | true =>
      simp only [d6299, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6300 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6300, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76942 q = 1) (hb : d81757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76942, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76943 q = 1) (hb : d81758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76943, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76944 q = 1) (hb : d81759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76944, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76945 q = 1) (hb : d81760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76945, d81760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76945, d81760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro10883 (p : Pattern) (ha : d6315 p = 1) (hb : d81762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5030 q = 1) (hb : d69120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7949 q ha hb
    | true =>
      simp only [d5030, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5031 q = 1) (hb : d69121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5031, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5032 q = 1) (hb : d81751 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5032, d81751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5032, d81751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5033 q = 1) (hb : d81752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5033, d81752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5033, d81752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5034 q = 1) (hb : d81753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5034, d81753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5034, d81753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6315 q = 1) (hb : d81762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6315, d81762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6315, d81762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro10884 (p : Pattern) (ha : d76950 p = 1) (hb : d81768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6278 q = 1) (hb : d52767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6278, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8973 q ha hb
    | true =>
      simp only [d6278, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d6279 q = 1) (hb : d52768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6279, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6280 q = 1) (hb : d52769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6280, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6281 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6281, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6285 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6285, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8974 q ha hb
    | true =>
      simp only [d6285, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d6286 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6286, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6287 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6287, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6292 q = 1) (hb : d81755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, d81755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8975 q ha hb
    | true =>
      simp only [d6292, d81755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8963 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76941 q = 1) (hb : d81756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76941, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76941, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6299 q = 1) (hb : d76041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7534 q ha hb
    | true =>
      simp only [d6299, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6300 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6300, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76942 q = 1) (hb : d81757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76942, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76943 q = 1) (hb : d81758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76943, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76944 q = 1) (hb : d81759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76944, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6306 q = 1) (hb : d52819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6306, d52819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8977 q ha hb
    | true =>
      simp only [d6306, d52819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro193 q ha hb
  have h17 (q : Pattern) (ha : d6307 q = 1) (hb : d52820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6307, d52820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6307, d52820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6308 q = 1) (hb : d52821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6308, d52821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d6308, d52821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d6309 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6309, d52822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6309, d52822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6311 q = 1) (hb : d52825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6311, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8978 q ha hb
    | true =>
      simp only [d6311, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro195 q ha hb
  have h21 (q : Pattern) (ha : d6312 q = 1) (hb : d52826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6312, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6312, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d6313 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6313, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d6313, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d6316 q = 1) (hb : d81763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, d81763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8969 q ha hb
    | true =>
      simp only [d6316, d81763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10883 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d76946 q = 1) (hb : d81764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76946, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76946, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d6320 q = 1) (hb : d76060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7537 q ha hb
    | true =>
      simp only [d6320, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d6321 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d6321, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d76947 q = 1) (hb : d81765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76947, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d76948 q = 1) (hb : d81766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76948, d81766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76948, d81766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d76949 q = 1) (hb : d81767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76949, d81767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76949, d81767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76950 q = 1) (hb : d81768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76950, d81768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76950, d81768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro10885 (p : Pattern) (ha : d76957 p = 1) (hb : d81782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6316 q = 1) (hb : d81763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, d81763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8969 q ha hb
    | true =>
      simp only [d6316, d81763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10883 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76946 q = 1) (hb : d81764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76946, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76946, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6320 q = 1) (hb : d76060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7537 q ha hb
    | true =>
      simp only [d6320, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6321 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6321, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76947 q = 1) (hb : d81765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76947, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76955 q = 1) (hb : d81780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76955, d81780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76955, d81780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76956 q = 1) (hb : d81781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76956, d81781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76956, d81781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76957 q = 1) (hb : d81782 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76957, d81782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76957, d81782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10886 (p : Pattern) (ha : d6349 p = 1) (hb : d76089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1393 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1394 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1395 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1395, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6349 q = 1) (hb : d76089 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6349, d76089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6349, d76089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro10887 (p : Pattern) (ha : d6355 p = 1) (hb : d76095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6350 q = 1) (hb : d76090 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, d76090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6350, d76090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7947 q ha hb
  have h2 (q : Pattern) (ha : d5018 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7947 q ha hb
    | true =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6351 q = 1) (hb : d76091 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6351, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5019 q = 1) (hb : d69109 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6352 q = 1) (hb : d76092 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6352, d76092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6352, d76092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6353 q = 1) (hb : d76093 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6353, d76093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6353, d76093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6354 q = 1) (hb : d76094 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, d76094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6354, d76094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6355 q = 1) (hb : d76095 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6355, d76095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6355, d76095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10888 (p : Pattern) (ha : d6361 p = 1) (hb : d76101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1412 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro168 q ha hb
  have h5 (q : Pattern) (ha : d1413 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1414 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1415 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1415, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6356 q = 1) (hb : d76096 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d76096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q ha hb
    | true =>
      simp only [d6356, d76096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10887 q ha hb
  have h9 (q : Pattern) (ha : d6357 q = 1) (hb : d76097 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d76097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d76097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6358 q = 1) (hb : d76098 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d76098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d76098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6359 q = 1) (hb : d76099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d76099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6359, d76099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6360 q = 1) (hb : d76100 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6360, d76100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6360, d76100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6361 q = 1) (hb : d76101 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6361, d76101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6361, d76101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro10889 (p : Pattern) (ha : d6367 p = 1) (hb : d81800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6362 q = 1) (hb : d76102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6362, d76102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10888 q ha hb
    | true =>
      simp only [d6362, d76102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6363 q = 1) (hb : d76103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6363, d76103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6363, d76103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6364 q = 1) (hb : d81797 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6364, d81797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6364, d81797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6365 q = 1) (hb : d81798 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6365, d81798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6365, d81798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6366 q = 1) (hb : d81799 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6366, d81799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6366, d81799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6367 q = 1) (hb : d81800 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6367, d81800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6367, d81800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro10890 (p : Pattern) (ha : d76967 p = 1) (hb : d81806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6368 q = 1) (hb : d81801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6368, d81801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8971 q ha hb
    | true =>
      simp only [d6368, d81801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10889 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52930 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76963 q = 1) (hb : d81802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76963, d81802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76963, d81802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6379 q = 1) (hb : d76115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6379, d76115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7542 q ha hb
    | true =>
      simp only [d6379, d76115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6380 q = 1) (hb : d76116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6380, d76116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6380, d76116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76964 q = 1) (hb : d81803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76964, d81803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76964, d81803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76965 q = 1) (hb : d81804 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76965, d81804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76965, d81804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76966 q = 1) (hb : d81805 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76966, d81805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76966, d81805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76967 q = 1) (hb : d81806 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76967, d81806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76967, d81806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10891 (p : Pattern) (ha : d76973 p = 1) (hb : d81812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6264 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6264, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6264, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10879 q ha hb
  have h2 (q : Pattern) (ha : d6265 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6265, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6265, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6273 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6273, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10879 q ha hb
    | true =>
      simp only [d6273, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10880 q ha hb
  have h4 (q : Pattern) (ha : d6274 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6274, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6274, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6275 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6275, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6275, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76951 q = 1) (hb : d81769 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76951, d81769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10882 q ha hb
    | true =>
      simp only [d76951, d81769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10884 q ha hb
  have h7 (q : Pattern) (ha : d6333 q = 1) (hb : d81776 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6333, d81776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10881 q ha hb
    | true =>
      simp only [d6333, d81776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q ha hb
  have h8 (q : Pattern) (ha : d76952 q = 1) (hb : d81777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76952, d81777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76952, d81777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76953 q = 1) (hb : d81778 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76953, d81778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76953, d81778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d76954 q = 1) (hb : d81779 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76954, d81779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76954, d81779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76958 q = 1) (hb : d81783 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76958, d81783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76958, d81783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10885 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro166 q ha hb
  have h13 (q : Pattern) (ha : d76959 q = 1) (hb : d81784 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76959, d81784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76959, d81784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76960 q = 1) (hb : d81785 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76960, d81785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76960, d81785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d76961 q = 1) (hb : d81786 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76961, d81786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76961, d81786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76962 q = 1) (hb : d81787 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76962, d81787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76962, d81787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76968 q = 1) (hb : d81807 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76968, d81807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76968, d81807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10890 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro171 q ha hb
  have h19 (q : Pattern) (ha : d76969 q = 1) (hb : d81808 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76969, d81808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76969, d81808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76970 q = 1) (hb : d81809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76970, d81809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76970, d81809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d76971 q = 1) (hb : d81810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76971, d81810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76971, d81810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76972 q = 1) (hb : d81811 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76972, d81811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76972, d81811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76973 q = 1) (hb : d81812 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76973, d81812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76973, d81812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro10892 (p : Pattern) (ha : d76979 p = 1) (hb : d81818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76974 q = 1) (hb : d81813 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76974, d81813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76974, d81813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10891 q ha hb
  have h2 (q : Pattern) (ha : d76975 q = 1) (hb : d81814 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76975, d81814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76975, d81814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76976 q = 1) (hb : d81815 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76976, d81815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76976, d81815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76977 q = 1) (hb : d81816 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76977, d81816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76977, d81816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76978 q = 1) (hb : d81817 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76978, d81817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76978, d81817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76979 q = 1) (hb : d81818 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76979, d81818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76979, d81818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10893 (p : Pattern) (ha : d6409 p = 1) (hb : d53070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6404 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8984 q ha hb
    | true =>
      simp only [d6404, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d6405 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6405, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6406 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6406, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6407 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6407, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6408 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6409 q = 1) (hb : d53070 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6409, d53070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6409, d53070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10894 (p : Pattern) (ha : d6418 p = 1) (hb : d53080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6404 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8984 q ha hb
    | true =>
      simp only [d6404, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d6405 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6405, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6406 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6406, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6407 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6407, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6408 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6413 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6413, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8986 q ha hb
    | true =>
      simp only [d6413, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h7 (q : Pattern) (ha : d6414 q = 1) (hb : d53076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d53076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6414, d53076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6415 q = 1) (hb : d53077 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, d53077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6415, d53077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6416 q = 1) (hb : d53078 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, d53078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6416, d53078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6417 q = 1) (hb : d53079 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, d53079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6417, d53079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6418 q = 1) (hb : d53080 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6418, d53080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6418, d53080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10895 (p : Pattern) (ha : d6478 p = 1) (hb : d81855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6473 q = 1) (hb : d81850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6473, d81850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8982 q ha hb
    | true =>
      simp only [d6473, d81850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d6474 q = 1) (hb : d81851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6474, d81851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6474, d81851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6475 q = 1) (hb : d81852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6475, d81852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6475, d81852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6476 q = 1) (hb : d81853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6476, d81853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6476, d81853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6477 q = 1) (hb : d81854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6477, d81854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6477, d81854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d53153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
    | true =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d53154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d53155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d53156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6478 q = 1) (hb : d81855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6478, d81855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6478, d81855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10896 (p : Pattern) (ha : d76987 p = 1) (hb : d81840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6424 q = 1) (hb : d53088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6424, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8992 q ha hb
    | true =>
      simp only [d6424, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d6425 q = 1) (hb : d53089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6425, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6426 q = 1) (hb : d53090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6426, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6427 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6427, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6431 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6431, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8993 q ha hb
    | true =>
      simp only [d6431, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d6432 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6432, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6433 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6433, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6438 q = 1) (hb : d81835 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, d81835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8994 q ha hb
    | true =>
      simp only [d6438, d81835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8982 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76983 q = 1) (hb : d81836 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76983, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76983, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6445 q = 1) (hb : d76176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7546 q ha hb
    | true =>
      simp only [d6445, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6446 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6446, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76984 q = 1) (hb : d81837 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76984, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76985 q = 1) (hb : d81838 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76985, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76986 q = 1) (hb : d81839 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76986, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76987 q = 1) (hb : d81840 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76987, d81840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76987, d81840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro10897 (p : Pattern) (ha : d6461 p = 1) (hb : d81842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5146 q = 1) (hb : d69233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7966 q ha hb
    | true =>
      simp only [d5146, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5147 q = 1) (hb : d69234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5147, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5148 q = 1) (hb : d81831 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5148, d81831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5148, d81831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5149 q = 1) (hb : d81832 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5149, d81832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5149, d81832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5150 q = 1) (hb : d81833 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5150, d81833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5150, d81833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6461 q = 1) (hb : d81842 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6461, d81842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6461, d81842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro10898 (p : Pattern) (ha : d76992 p = 1) (hb : d81848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6424 q = 1) (hb : d53088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6424, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8992 q ha hb
    | true =>
      simp only [d6424, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d6425 q = 1) (hb : d53089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6425, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6426 q = 1) (hb : d53090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6426, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6427 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6427, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6431 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6431, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8993 q ha hb
    | true =>
      simp only [d6431, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d6432 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6432, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6433 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6433, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6438 q = 1) (hb : d81835 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, d81835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8994 q ha hb
    | true =>
      simp only [d6438, d81835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8982 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76983 q = 1) (hb : d81836 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76983, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76983, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6445 q = 1) (hb : d76176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7546 q ha hb
    | true =>
      simp only [d6445, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6446 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6446, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76984 q = 1) (hb : d81837 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76984, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76985 q = 1) (hb : d81838 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76985, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76986 q = 1) (hb : d81839 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76986, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6452 q = 1) (hb : d53134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6452, d53134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8996 q ha hb
    | true =>
      simp only [d6452, d53134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro249 q ha hb
  have h17 (q : Pattern) (ha : d6453 q = 1) (hb : d53135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6453, d53135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6453, d53135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6454 q = 1) (hb : d53136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6454, d53136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d6454, d53136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d6455 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6455, d53137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6455, d53137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6457 q = 1) (hb : d53140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6457, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8997 q ha hb
    | true =>
      simp only [d6457, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro251 q ha hb
  have h21 (q : Pattern) (ha : d6458 q = 1) (hb : d53141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6458, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6458, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d6459 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6459, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d6459, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d6462 q = 1) (hb : d81843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, d81843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8988 q ha hb
    | true =>
      simp only [d6462, d81843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10897 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d76988 q = 1) (hb : d81844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76988, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76988, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d6466 q = 1) (hb : d76195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7549 q ha hb
    | true =>
      simp only [d6466, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d6467 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d6467, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d76989 q = 1) (hb : d81845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76989, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d76990 q = 1) (hb : d81846 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76990, d81846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76990, d81846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d76991 q = 1) (hb : d81847 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76991, d81847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76991, d81847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76992 q = 1) (hb : d81848 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76992, d81848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76992, d81848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro10899 (p : Pattern) (ha : d76999 p = 1) (hb : d81862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6462 q = 1) (hb : d81843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, d81843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8988 q ha hb
    | true =>
      simp only [d6462, d81843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10897 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76988 q = 1) (hb : d81844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76988, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76988, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6466 q = 1) (hb : d76195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7549 q ha hb
    | true =>
      simp only [d6466, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6467 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6467, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76989 q = 1) (hb : d81845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76989, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76997 q = 1) (hb : d81860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76997, d81860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76997, d81860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76998 q = 1) (hb : d81861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76998, d81861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76998, d81861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76999 q = 1) (hb : d81862 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76999, d81862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76999, d81862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10900 (p : Pattern) (ha : d6495 p = 1) (hb : d76224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1864 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1868 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
  have h8 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1869 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1870 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1871 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1872 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1872, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6495 q = 1) (hb : d76224 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6495, d76224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6495, d76224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro10901 (p : Pattern) (ha : d6501 p = 1) (hb : d76230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6496 q = 1) (hb : d76225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
  have h2 (q : Pattern) (ha : d5134 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
    | true =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6497 q = 1) (hb : d76226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6497, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5135 q = 1) (hb : d69222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6498 q = 1) (hb : d76227 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6498, d76227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6498, d76227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6499 q = 1) (hb : d76228 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6499, d76228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6499, d76228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6500 q = 1) (hb : d76229 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d76229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6500, d76229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6501 q = 1) (hb : d76230 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6501, d76230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6501, d76230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10902 (p : Pattern) (ha : d6507 p = 1) (hb : d76236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1889 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro226 q ha hb
  have h5 (q : Pattern) (ha : d1890 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1891 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1892 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1892, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6502 q = 1) (hb : d76231 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d76231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q ha hb
    | true =>
      simp only [d6502, d76231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10901 q ha hb
  have h9 (q : Pattern) (ha : d6503 q = 1) (hb : d76232 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d76232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d76232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6504 q = 1) (hb : d76233 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d76233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d76233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6505 q = 1) (hb : d76234 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d76234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6505, d76234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6506 q = 1) (hb : d76235 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6506, d76235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6506, d76235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6507 q = 1) (hb : d76236 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6507, d76236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6507, d76236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro10903 (p : Pattern) (ha : d6513 p = 1) (hb : d81880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6508 q = 1) (hb : d76237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6508, d76237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10902 q ha hb
    | true =>
      simp only [d6508, d76237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6509 q = 1) (hb : d76238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6509, d76238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6509, d76238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6510 q = 1) (hb : d81877 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6510, d81877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6510, d81877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6511 q = 1) (hb : d81878 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6511, d81878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6511, d81878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6512 q = 1) (hb : d81879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6512, d81879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6512, d81879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6513 q = 1) (hb : d81880 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6513, d81880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6513, d81880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro10904 (p : Pattern) (ha : d77009 p = 1) (hb : d81886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6514 q = 1) (hb : d81881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6514, d81881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8990 q ha hb
    | true =>
      simp only [d6514, d81881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10903 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77005 q = 1) (hb : d81882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77005, d81882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77005, d81882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6525 q = 1) (hb : d76250 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6525, d76250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7554 q ha hb
    | true =>
      simp only [d6525, d76250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6526 q = 1) (hb : d76251 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6526, d76251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6526, d76251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77006 q = 1) (hb : d81883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77006, d81883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77006, d81883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77007 q = 1) (hb : d81884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77007, d81884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77007, d81884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77008 q = 1) (hb : d81885 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77008, d81885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77008, d81885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77009 q = 1) (hb : d81886 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77009, d81886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77009, d81886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10905 (p : Pattern) (ha : d77015 p = 1) (hb : d81892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6410 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6410, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6410, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10893 q ha hb
  have h2 (q : Pattern) (ha : d6411 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6411, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6411, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6419 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6419, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10893 q ha hb
    | true =>
      simp only [d6419, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10894 q ha hb
  have h4 (q : Pattern) (ha : d6420 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6420, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6420, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6421 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6421, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6421, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76993 q = 1) (hb : d81849 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76993, d81849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10896 q ha hb
    | true =>
      simp only [d76993, d81849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10898 q ha hb
  have h7 (q : Pattern) (ha : d6479 q = 1) (hb : d81856 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6479, d81856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10895 q ha hb
    | true =>
      simp only [d6479, d81856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q ha hb
  have h8 (q : Pattern) (ha : d76994 q = 1) (hb : d81857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76994, d81857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76994, d81857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76995 q = 1) (hb : d81858 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76995, d81858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76995, d81858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d76996 q = 1) (hb : d81859 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76996, d81859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76996, d81859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77000 q = 1) (hb : d81863 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77000, d81863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77000, d81863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10899 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro224 q ha hb
  have h13 (q : Pattern) (ha : d77001 q = 1) (hb : d81864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77001, d81864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77001, d81864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77002 q = 1) (hb : d81865 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77002, d81865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77002, d81865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d77003 q = 1) (hb : d81866 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77003, d81866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d77003, d81866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77004 q = 1) (hb : d81867 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77004, d81867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77004, d81867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77010 q = 1) (hb : d81887 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77010, d81887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77010, d81887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10904 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro229 q ha hb
  have h19 (q : Pattern) (ha : d77011 q = 1) (hb : d81888 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77011, d81888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77011, d81888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d77012 q = 1) (hb : d81889 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77012, d81889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d77012, d81889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d77013 q = 1) (hb : d81890 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77013, d81890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d77013, d81890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d77014 q = 1) (hb : d81891 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77014, d81891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77014, d81891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d77015 q = 1) (hb : d81892 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77015, d81892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77015, d81892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro10906 (p : Pattern) (ha : d77021 p = 1) (hb : d81898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77016 q = 1) (hb : d81893 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77016, d81893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77016, d81893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10905 q ha hb
  have h2 (q : Pattern) (ha : d77017 q = 1) (hb : d81894 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77017, d81894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77017, d81894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77018 q = 1) (hb : d81895 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77018, d81895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77018, d81895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77019 q = 1) (hb : d81896 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77019, d81896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77019, d81896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77020 q = 1) (hb : d81897 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77020, d81897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77020, d81897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77021 q = 1) (hb : d81898 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77021, d81898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77021, d81898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10907 (p : Pattern) (ha : d6556 p = 1) (hb : d53391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6551 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9003 q ha hb
    | true =>
      simp only [d6551, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d6552 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6552, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6553 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6553, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6554 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6554, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6555 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6556 q = 1) (hb : d53391 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6556, d53391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6556, d53391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10908 (p : Pattern) (ha : d6565 p = 1) (hb : d53401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6551 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9003 q ha hb
    | true =>
      simp only [d6551, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d6552 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6552, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6553 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6553, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6554 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6554, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6555 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6560 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6560, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9005 q ha hb
    | true =>
      simp only [d6560, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h7 (q : Pattern) (ha : d6561 q = 1) (hb : d53397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d53397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6561, d53397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6562 q = 1) (hb : d53398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, d53398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6562, d53398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6563 q = 1) (hb : d53399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, d53399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6563, d53399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6564 q = 1) (hb : d53400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, d53400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6564, d53400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6565 q = 1) (hb : d53401 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6565, d53401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6565, d53401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10909 (p : Pattern) (ha : d6625 p = 1) (hb : d81936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6620 q = 1) (hb : d81931 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6620, d81931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9001 q ha hb
    | true =>
      simp only [d6620, d81931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d6621 q = 1) (hb : d81932 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6621, d81932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6621, d81932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6622 q = 1) (hb : d81933 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6622, d81933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6622, d81933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6623 q = 1) (hb : d81934 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6623, d81934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6623, d81934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6624 q = 1) (hb : d81935 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6624, d81935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6624, d81935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6625 q = 1) (hb : d81936 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6625, d81936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6625, d81936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10910 (p : Pattern) (ha : d77030 p = 1) (hb : d81921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6571 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6571, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9011 q ha hb
    | true =>
      simp only [d6571, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d6572 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6572, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6573 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6573, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6574 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6574, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6578 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6578, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9012 q ha hb
    | true =>
      simp only [d6578, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d6579 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6579, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6580 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6580, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6585 q = 1) (hb : d81916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, d81916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9013 q ha hb
    | true =>
      simp only [d6585, d81916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9001 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d77026 q = 1) (hb : d81917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77026, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77026, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6592 q = 1) (hb : d76312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7558 q ha hb
    | true =>
      simp only [d6592, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6593 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6593, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d77027 q = 1) (hb : d81918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77027, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77028 q = 1) (hb : d81919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77028, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77029 q = 1) (hb : d81920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77029, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77030 q = 1) (hb : d81921 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77030, d81921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77030, d81921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro10911 (p : Pattern) (ha : d6608 p = 1) (hb : d81923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5259 q = 1) (hb : d69343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7982 q ha hb
    | true =>
      simp only [d5259, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5260 q = 1) (hb : d69344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5260, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5261 q = 1) (hb : d81912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5261, d81912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5261, d81912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5262 q = 1) (hb : d81913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5262, d81913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5262, d81913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5263 q = 1) (hb : d81914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5263, d81914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5263, d81914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6608 q = 1) (hb : d81923 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6608, d81923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6608, d81923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro10912 (p : Pattern) (ha : d77035 p = 1) (hb : d81929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6571 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6571, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9011 q ha hb
    | true =>
      simp only [d6571, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d6572 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6572, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6573 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6573, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6574 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6574, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6578 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6578, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9012 q ha hb
    | true =>
      simp only [d6578, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d6579 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6579, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6580 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6580, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6585 q = 1) (hb : d81916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, d81916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9013 q ha hb
    | true =>
      simp only [d6585, d81916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9001 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d77026 q = 1) (hb : d81917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77026, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77026, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6592 q = 1) (hb : d76312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7558 q ha hb
    | true =>
      simp only [d6592, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6593 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6593, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d77027 q = 1) (hb : d81918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77027, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77028 q = 1) (hb : d81919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77028, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77029 q = 1) (hb : d81920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77029, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6599 q = 1) (hb : d53451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6599, d53451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9015 q ha hb
    | true =>
      simp only [d6599, d53451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro308 q ha hb
  have h17 (q : Pattern) (ha : d6600 q = 1) (hb : d53452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6600, d53452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6600, d53452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6601 q = 1) (hb : d53453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6601, d53453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d6601, d53453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d6602 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6602, d53454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6602, d53454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6604 q = 1) (hb : d53457 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6604, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9016 q ha hb
    | true =>
      simp only [d6604, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro310 q ha hb
  have h21 (q : Pattern) (ha : d6605 q = 1) (hb : d53458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6605, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6605, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d6606 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6606, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d6606, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d6609 q = 1) (hb : d81924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, d81924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9007 q ha hb
    | true =>
      simp only [d6609, d81924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10911 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d77031 q = 1) (hb : d81925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77031, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d77031, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d6613 q = 1) (hb : d76331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7561 q ha hb
    | true =>
      simp only [d6613, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d6614 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d6614, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d77032 q = 1) (hb : d81926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d77032, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d77033 q = 1) (hb : d81927 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77033, d81927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d77033, d81927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d77034 q = 1) (hb : d81928 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77034, d81928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d77034, d81928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d77035 q = 1) (hb : d81929 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77035, d81929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77035, d81929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro10913 (p : Pattern) (ha : d77042 p = 1) (hb : d81943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6609 q = 1) (hb : d81924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, d81924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9007 q ha hb
    | true =>
      simp only [d6609, d81924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10911 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77031 q = 1) (hb : d81925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77031, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77031, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6613 q = 1) (hb : d76331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7561 q ha hb
    | true =>
      simp only [d6613, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6614 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6614, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77032 q = 1) (hb : d81926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77032, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77040 q = 1) (hb : d81941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77040, d81941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77040, d81941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77041 q = 1) (hb : d81942 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77041, d81942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77041, d81942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77042 q = 1) (hb : d81943 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77042, d81943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77042, d81943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10914 (p : Pattern) (ha : d6642 p = 1) (hb : d76360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2340 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2341 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2342 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2343 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h8 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2347 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2348 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2349 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2350 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2350, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6642 q = 1) (hb : d76360 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6642, d76360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6642, d76360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro10915 (p : Pattern) (ha : d6648 p = 1) (hb : d76366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6643 q = 1) (hb : d76361 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
  have h2 (q : Pattern) (ha : d5247 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
    | true =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6644 q = 1) (hb : d76362 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6644, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5248 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6645 q = 1) (hb : d76363 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6645, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6645, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6646 q = 1) (hb : d76364 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6646, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6646, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6647 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6647, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6648 q = 1) (hb : d76366 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6648, d76366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6648, d76366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10916 (p : Pattern) (ha : d6654 p = 1) (hb : d76372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2367 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro285 q ha hb
  have h5 (q : Pattern) (ha : d2368 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2369 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2370 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2370, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6649 q = 1) (hb : d76367 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d76367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10914 q ha hb
    | true =>
      simp only [d6649, d76367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10915 q ha hb
  have h9 (q : Pattern) (ha : d6650 q = 1) (hb : d76368 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d76368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d76368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6651 q = 1) (hb : d76369 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d76369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d76369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6652 q = 1) (hb : d76370 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d76370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6652, d76370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6653 q = 1) (hb : d76371 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6653, d76371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6653, d76371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6654 q = 1) (hb : d76372 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6654, d76372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6654, d76372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro10917 (p : Pattern) (ha : d6660 p = 1) (hb : d81961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6655 q = 1) (hb : d76373 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6655, d76373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10916 q ha hb
    | true =>
      simp only [d6655, d76373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6656 q = 1) (hb : d76374 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6656, d76374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6656, d76374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6657 q = 1) (hb : d81958 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6657, d81958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6657, d81958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6658 q = 1) (hb : d81959 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6658, d81959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6658, d81959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6659 q = 1) (hb : d81960 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6659, d81960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6659, d81960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6660 q = 1) (hb : d81961 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6660, d81961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6660, d81961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro10918 (p : Pattern) (ha : d77052 p = 1) (hb : d81967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6661 q = 1) (hb : d81962 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6661, d81962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9009 q ha hb
    | true =>
      simp only [d6661, d81962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10917 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53562 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77048 q = 1) (hb : d81963 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77048, d81963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77048, d81963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6672 q = 1) (hb : d76386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, d76386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7566 q ha hb
    | true =>
      simp only [d6672, d76386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6673 q = 1) (hb : d76387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6673, d76387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6673, d76387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77049 q = 1) (hb : d81964 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77049, d81964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77049, d81964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77050 q = 1) (hb : d81965 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77050, d81965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77050, d81965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77051 q = 1) (hb : d81966 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77051, d81966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77051, d81966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77052 q = 1) (hb : d81967 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77052, d81967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77052, d81967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro10919 (p : Pattern) (ha : d77058 p = 1) (hb : d81973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6557 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6557, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6557, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10907 q ha hb
  have h2 (q : Pattern) (ha : d6558 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6558, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6558, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6566 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6566, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10907 q ha hb
    | true =>
      simp only [d6566, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10908 q ha hb
  have h4 (q : Pattern) (ha : d6567 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6567, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6567, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6568 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6568, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6568, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77036 q = 1) (hb : d81930 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77036, d81930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10910 q ha hb
    | true =>
      simp only [d77036, d81930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10912 q ha hb
  have h7 (q : Pattern) (ha : d6626 q = 1) (hb : d81937 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6626, d81937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10909 q ha hb
    | true =>
      simp only [d6626, d81937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q ha hb
  have h8 (q : Pattern) (ha : d77037 q = 1) (hb : d81938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77037, d81938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77037, d81938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77038 q = 1) (hb : d81939 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77038, d81939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77038, d81939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d77039 q = 1) (hb : d81940 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77039, d81940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77039, d81940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77043 q = 1) (hb : d81944 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77043, d81944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77043, d81944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10913 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro283 q ha hb
  have h13 (q : Pattern) (ha : d77044 q = 1) (hb : d81945 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77044, d81945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77044, d81945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77045 q = 1) (hb : d81946 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77045, d81946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77045, d81946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d77046 q = 1) (hb : d81947 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77046, d81947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d77046, d81947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77047 q = 1) (hb : d81948 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77047, d81948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77047, d81948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77053 q = 1) (hb : d81968 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77053, d81968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77053, d81968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10918 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro288 q ha hb
  have h19 (q : Pattern) (ha : d77054 q = 1) (hb : d81969 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77054, d81969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77054, d81969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d77055 q = 1) (hb : d81970 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77055, d81970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d77055, d81970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d77056 q = 1) (hb : d81971 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77056, d81971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d77056, d81971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d77057 q = 1) (hb : d81972 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77057, d81972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77057, d81972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d77058 q = 1) (hb : d81973 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77058, d81973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77058, d81973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro10920 (p : Pattern) (ha : d77064 p = 1) (hb : d81979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77059 q = 1) (hb : d81974 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77059, d81974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77059, d81974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10919 q ha hb
  have h2 (q : Pattern) (ha : d77060 q = 1) (hb : d81975 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77060, d81975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77060, d81975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77061 q = 1) (hb : d81976 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77061, d81976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77061, d81976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77062 q = 1) (hb : d81977 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77062, d81977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77062, d81977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77063 q = 1) (hb : d81978 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77063, d81978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77063, d81978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77064 q = 1) (hb : d81979 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77064, d81979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77064, d81979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10921 (p : Pattern) (ha : d77070 p = 1) (hb : d81985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d76899 q = 1) (hb : d81662 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76899, d81662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10852 q ha hb
    | true =>
      simp only [d76899, d81662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10865 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76939 q = 1) (hb : d81740 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76939, d81740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76939, d81740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10878 q ha hb
  have h3 (q : Pattern) (ha : d76940 q = 1) (hb : d81741 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76940, d81741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76940, d81741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76980 q = 1) (hb : d81819 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76980, d81819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76980, d81819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10892 q ha hb
  have h5 (q : Pattern) (ha : d76981 q = 1) (hb : d81820 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76981, d81820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76981, d81820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76982 q = 1) (hb : d81821 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76982, d81821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76982, d81821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77022 q = 1) (hb : d81899 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77022, d81899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77022, d81899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10906 q ha hb
  have h8 (q : Pattern) (ha : d77023 q = 1) (hb : d81900 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77023, d81900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77023, d81900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77024 q = 1) (hb : d81901 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77024, d81901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77024, d81901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77025 q = 1) (hb : d81902 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77025, d81902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77025, d81902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77065 q = 1) (hb : d81980 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77065, d81980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77065, d81980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10920 q ha hb
  have h12 (q : Pattern) (ha : d77066 q = 1) (hb : d81981 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77066, d81981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77066, d81981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77067 q = 1) (hb : d81982 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77067, d81982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77067, d81982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77068 q = 1) (hb : d81983 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77068, d81983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77068, d81983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77069 q = 1) (hb : d81984 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d77069, d81984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77069, d81984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77070 q = 1) (hb : d81985 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d77070, d81985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77070, d81985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro10922 (p : Pattern) (ha : d77076 p = 1) (hb : d81991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77071 q = 1) (hb : d81986 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d77071, d81986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10921 q ha hb
    | true =>
      simp only [d77071, d81986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77072 q = 1) (hb : d81987 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d77072, d81987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77072, d81987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77073 q = 1) (hb : d81988 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d77073, d81988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77073, d81988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77074 q = 1) (hb : d81989 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d77074, d81989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77074, d81989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77075 q = 1) (hb : d81990 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d77075, d81990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77075, d81990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77076 q = 1) (hb : d81991 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d77076, d81991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77076, d81991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10923 (p : Pattern) (ha : d77082 p = 1) (hb : d81997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77077 q = 1) (hb : d81992 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d77077, d81992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10922 q ha hb
    | true =>
      simp only [d77077, d81992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77078 q = 1) (hb : d81993 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d77078, d81993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77078, d81993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77079 q = 1) (hb : d81994 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d77079, d81994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77079, d81994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77080 q = 1) (hb : d81995 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d77080, d81995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77080, d81995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77081 q = 1) (hb : d81996 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d77081, d81996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77081, d81996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77082 q = 1) (hb : d81997 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d77082, d81997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77082, d81997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10924 (p : Pattern) (ha : d77088 p = 1) (hb : d82003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77083 q = 1) (hb : d81998 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d77083, d81998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10923 q ha hb
    | true =>
      simp only [d77083, d81998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77084 q = 1) (hb : d81999 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d77084, d81999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77084, d81999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77085 q = 1) (hb : d82000 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d77085, d82000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77085, d82000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77086 q = 1) (hb : d82001 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d77086, d82001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77086, d82001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77087 q = 1) (hb : d82002 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d77087, d82002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77087, d82002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77088 q = 1) (hb : d82003 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d77088, d82003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77088, d82003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10925 (p : Pattern) (ha : d77094 p = 1) (hb : d82009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77089 q = 1) (hb : d82004 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d77089, d82004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10924 q ha hb
    | true =>
      simp only [d77089, d82004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77090 q = 1) (hb : d82005 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d77090, d82005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77090, d82005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77091 q = 1) (hb : d82006 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d77091, d82006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77091, d82006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77092 q = 1) (hb : d82007 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d77092, d82007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77092, d82007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77093 q = 1) (hb : d82008 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d77093, d82008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77093, d82008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77094 q = 1) (hb : d82009 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d77094, d82009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77094, d82009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10926 (p : Pattern) (ha : d77100 p = 1) (hb : d82015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77095 q = 1) (hb : d82010 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d77095, d82010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10925 q ha hb
    | true =>
      simp only [d77095, d82010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77096 q = 1) (hb : d82011 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d77096, d82011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77096, d82011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77097 q = 1) (hb : d82012 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d77097, d82012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77097, d82012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77098 q = 1) (hb : d82013 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d77098, d82013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77098, d82013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77099 q = 1) (hb : d82014 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d77099, d82014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77099, d82014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77100 q = 1) (hb : d82015 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d77100, d82015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77100, d82015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10927 (p : Pattern) (ha : d77106 p = 1) (hb : d82021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77101 q = 1) (hb : d82016 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d77101, d82016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10926 q ha hb
    | true =>
      simp only [d77101, d82016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77102 q = 1) (hb : d82017 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d77102, d82017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77102, d82017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77103 q = 1) (hb : d82018 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d77103, d82018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77103, d82018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77104 q = 1) (hb : d82019 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d77104, d82019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77104, d82019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77105 q = 1) (hb : d82020 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d77105, d82020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77105, d82020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77106 q = 1) (hb : d82021 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d77106, d82021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77106, d82021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10928 (p : Pattern) (ha : d77112 p = 1) (hb : d82027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77107 q = 1) (hb : d82022 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d77107, d82022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10927 q ha hb
    | true =>
      simp only [d77107, d82022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77108 q = 1) (hb : d82023 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d77108, d82023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77108, d82023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77109 q = 1) (hb : d82024 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d77109, d82024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77109, d82024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77110 q = 1) (hb : d82025 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d77110, d82025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77110, d82025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77111 q = 1) (hb : d82026 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d77111, d82026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77111, d82026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77112 q = 1) (hb : d82027 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d77112, d82027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77112, d82027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10929 (p : Pattern) (ha : d82907 p = 1) (hb : d89600 p = 1) : d82907 p = 1 := by
  have h0 (q : Pattern) (ha : d82907 q = 1) (hb : d89600 q = 1) : d82907 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro10930 (p : Pattern) (ha : d5895 p = 1) (hb : d81539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81534 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5850 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d5891 q = 1) (hb : d81535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5891, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5892 q = 1) (hb : d81536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5892, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5893 q = 1) (hb : d81537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5893, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5894 q = 1) (hb : d81538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5894, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5895 q = 1) (hb : d81539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5895, d81539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5895, d81539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10931 (p : Pattern) (ha : d5902 p = 1) (hb : d81546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81534 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5850 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d5850, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d5891 q = 1) (hb : d81535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5891, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5892 q = 1) (hb : d81536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5892, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5893 q = 1) (hb : d81537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5893, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5894 q = 1) (hb : d81538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d81541 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d5856 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
    | true =>
      simp only [d5856, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d5898 q = 1) (hb : d81542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5898, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5899 q = 1) (hb : d81543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5899, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5900 q = 1) (hb : d81544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, d81544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5900, d81544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5901 q = 1) (hb : d81545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, d81545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5901, d81545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d5902 q = 1) (hb : d81546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5902, d81546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5902, d81546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10932 (p : Pattern) (ha : d81553 p = 1) (hb : d82697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81541 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5856 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
    | true =>
      simp only [d5856, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d5898 q = 1) (hb : d81542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5898, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5899 q = 1) (hb : d81543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5899, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5900 q = 1) (hb : d81551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, d81551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5900, d81551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5901 q = 1) (hb : d81552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, d81552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5901, d81552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81553 q = 1) (hb : d82697 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81553, d82697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81553, d82697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10933 (p : Pattern) (ha : d81572 p = 1) (hb : d82707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81567 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5874 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5874, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8906 q ha hb
    | true =>
      simp only [d5874, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d81568 q = 1) (hb : d82703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81568, d82703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81568, d82703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81569 q = 1) (hb : d82704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81569, d82704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81569, d82704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81570 q = 1) (hb : d82705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81570, d82705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81570, d82705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81571 q = 1) (hb : d82706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81571, d82706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81571, d82706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81572 q = 1) (hb : d82707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81572, d82707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81572, d82707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10934 (p : Pattern) (ha : d81578 p = 1) (hb : d82713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5903 q = 1) (hb : d81547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5903, d81547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10930 q ha hb
    | true =>
      simp only [d5903, d81547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10931 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5904 q = 1) (hb : d81548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5904, d81548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5904, d81548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81549 q = 1) (hb : d82695 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81549, d82695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81549, d82695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81550 q = 1) (hb : d82696 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81550, d82696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81550, d82696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81554 q = 1) (hb : d82698 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81554, d82698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81554, d82698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10932 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d81555 q = 1) (hb : d82699 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81555, d82699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81555, d82699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81556 q = 1) (hb : d82700 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81556, d82700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81556, d82700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d81557 q = 1) (hb : d82701 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81557, d82701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81557, d82701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d81558 q = 1) (hb : d82702 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81558, d82702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81558, d82702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81573 q = 1) (hb : d82708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81573, d82708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81573, d82708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10933 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d81574 q = 1) (hb : d82709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81574, d82709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81574, d82709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d81575 q = 1) (hb : d82710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81575, d82710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81575, d82710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d81576 q = 1) (hb : d82711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81576, d82711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81576, d82711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d81577 q = 1) (hb : d82712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81577, d82712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81577, d82712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d81578 q = 1) (hb : d82713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81578, d82713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d81578, d82713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10935 (p : Pattern) (ha : d81584 p = 1) (hb : d82719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52074 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro327 q ha hb
  have h3 (q : Pattern) (ha : d52075 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52076 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52077 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52078 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81579 q = 1) (hb : d82714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81579, d82714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81579, d82714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10934 q ha hb
  have h8 (q : Pattern) (ha : d81580 q = 1) (hb : d82715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81580, d82715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81580, d82715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81581 q = 1) (hb : d82716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81581, d82716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81581, d82716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81582 q = 1) (hb : d82717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81582, d82717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81582, d82717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d81583 q = 1) (hb : d82718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81583, d82718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81583, d82718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d81584 q = 1) (hb : d82719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81584, d82719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81584, d82719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro10936 (p : Pattern) (ha : d5997 p = 1) (hb : d81603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81598 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5992 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5992, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8927 q ha hb
    | true =>
      simp only [d5992, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h5 (q : Pattern) (ha : d5993 q = 1) (hb : d81599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5993, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5994 q = 1) (hb : d81600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5994, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5995 q = 1) (hb : d81601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5995, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5996 q = 1) (hb : d81602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5996, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5997 q = 1) (hb : d81603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5997, d81603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5997, d81603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10937 (p : Pattern) (ha : d6005 p = 1) (hb : d81611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5992 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5992, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8927 q ha hb
    | true =>
      simp only [d5992, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h4 (q : Pattern) (ha : d5993 q = 1) (hb : d81599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5993, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5994 q = 1) (hb : d81600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5994, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5995 q = 1) (hb : d81601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5995, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5996 q = 1) (hb : d81602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d81606 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6000 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6000, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8929 q ha hb
    | true =>
      simp only [d6000, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h13 (q : Pattern) (ha : d6001 q = 1) (hb : d81607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6001, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6002 q = 1) (hb : d81608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6002, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6003 q = 1) (hb : d81609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, d81609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6003, d81609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6004 q = 1) (hb : d81610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, d81610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6004, d81610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6005 q = 1) (hb : d81611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6005, d81611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6005, d81611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10938 (p : Pattern) (ha : d81625 p = 1) (hb : d82722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81606 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6000 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6000, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8929 q ha hb
    | true =>
      simp only [d6000, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h3 (q : Pattern) (ha : d6001 q = 1) (hb : d81607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6001, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6002 q = 1) (hb : d81608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6002, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6003 q = 1) (hb : d81623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, d81623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6003, d81623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6004 q = 1) (hb : d81624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, d81624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6004, d81624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81625 q = 1) (hb : d82722 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81625, d82722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81625, d82722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10939 (p : Pattern) (ha : d81649 p = 1) (hb : d82733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52399 q = 1) (hb : d82728 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52399, d82728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9040 q hb ha
    | true =>
      simp only [d52399, d82728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72 q hb ha
  have h3 (q : Pattern) (ha : d81645 q = 1) (hb : d82729 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81645, d82729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81645, d82729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81646 q = 1) (hb : d82730 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81646, d82730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81646, d82730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81647 q = 1) (hb : d82731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81647, d82731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81647, d82731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81648 q = 1) (hb : d82732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81648, d82732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81648, d82732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81649 q = 1) (hb : d82733 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81649, d82733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81649, d82733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10940 (p : Pattern) (ha : d81655 p = 1) (hb : d82739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6006 q = 1) (hb : d81612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6006, d81612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10936 q ha hb
    | true =>
      simp only [d6006, d81612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10937 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81619 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6007 q = 1) (hb : d81620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6007, d81620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6007, d81620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81621 q = 1) (hb : d82720 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81621, d82720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81621, d82720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81622 q = 1) (hb : d82721 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81622, d82721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81622, d82721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81626 q = 1) (hb : d82723 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81626, d82723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81626, d82723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10938 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d81627 q = 1) (hb : d82724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81627, d82724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81627, d82724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81628 q = 1) (hb : d82725 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81628, d82725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81628, d82725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d81629 q = 1) (hb : d82726 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81629, d82726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81629, d82726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d81630 q = 1) (hb : d82727 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81630, d82727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81630, d82727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81650 q = 1) (hb : d82734 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81650, d82734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81650, d82734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10939 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d81651 q = 1) (hb : d82735 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81651, d82735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81651, d82735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d81652 q = 1) (hb : d82736 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81652, d82736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81652, d82736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d81653 q = 1) (hb : d82737 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81653, d82737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81653, d82737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d81654 q = 1) (hb : d82738 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81654, d82738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81654, d82738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d81655 q = 1) (hb : d82739 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81655, d82739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d81655, d82739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10941 (p : Pattern) (ha : d81661 p = 1) (hb : d82745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81656 q = 1) (hb : d82740 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81656, d82740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81656, d82740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10940 q ha hb
  have h2 (q : Pattern) (ha : d81657 q = 1) (hb : d82741 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81657, d82741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81657, d82741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81658 q = 1) (hb : d82742 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81658, d82742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81658, d82742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81659 q = 1) (hb : d82743 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81659, d82743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81659, d82743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81660 q = 1) (hb : d82744 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81660, d82744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81660, d82744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81661 q = 1) (hb : d82745 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81661, d82745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81661, d82745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10942 (p : Pattern) (ha : d6124 p = 1) (hb : d81681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81676 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6119 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6119, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8946 q ha hb
    | true =>
      simp only [d6119, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h5 (q : Pattern) (ha : d6120 q = 1) (hb : d81677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6120, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6121 q = 1) (hb : d81678 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6121, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6122 q = 1) (hb : d81679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6122, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6123 q = 1) (hb : d81680 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6123, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6124 q = 1) (hb : d81681 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6124, d81681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6124, d81681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10943 (p : Pattern) (ha : d6133 p = 1) (hb : d81689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81676 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6119 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6119, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8946 q ha hb
    | true =>
      simp only [d6119, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h4 (q : Pattern) (ha : d6120 q = 1) (hb : d81677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6120, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6121 q = 1) (hb : d81678 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6121, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6122 q = 1) (hb : d81679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6122, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6123 q = 1) (hb : d81680 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d81684 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6128 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6128, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8948 q ha hb
    | true =>
      simp only [d6128, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h13 (q : Pattern) (ha : d6129 q = 1) (hb : d81685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6129, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6130 q = 1) (hb : d81686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6130, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6131 q = 1) (hb : d81687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, d81687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6131, d81687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6132 q = 1) (hb : d81688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, d81688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6132, d81688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6133 q = 1) (hb : d81689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6133, d81689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6133, d81689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10944 (p : Pattern) (ha : d81703 p = 1) (hb : d82749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6128 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6128, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8948 q ha hb
    | true =>
      simp only [d6128, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h3 (q : Pattern) (ha : d6129 q = 1) (hb : d81685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6129, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6130 q = 1) (hb : d81686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6130, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6131 q = 1) (hb : d81701 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, d81701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6131, d81701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6132 q = 1) (hb : d81702 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, d81702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6132, d81702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81703 q = 1) (hb : d82749 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81703, d82749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81703, d82749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10945 (p : Pattern) (ha : d81727 p = 1) (hb : d82760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81722 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52636 q = 1) (hb : d82755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52636, d82755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9047 q hb ha
    | true =>
      simp only [d52636, d82755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro118 q hb ha
  have h3 (q : Pattern) (ha : d81723 q = 1) (hb : d82756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81723, d82756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81723, d82756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d75982 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81724 q = 1) (hb : d82757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81724, d82757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81724, d82757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81725 q = 1) (hb : d82758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81725, d82758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81725, d82758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81726 q = 1) (hb : d82759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81726, d82759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81726, d82759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81727 q = 1) (hb : d82760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81727, d82760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81727, d82760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10946 (p : Pattern) (ha : d81733 p = 1) (hb : d82766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6134 q = 1) (hb : d81690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6134, d81690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10942 q ha hb
    | true =>
      simp only [d6134, d81690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10943 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6135 q = 1) (hb : d81698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6135, d81698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6135, d81698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81699 q = 1) (hb : d82747 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81699, d82747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81699, d82747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81700 q = 1) (hb : d82748 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81700, d82748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81700, d82748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81704 q = 1) (hb : d82750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81704, d82750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81704, d82750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10944 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d81705 q = 1) (hb : d82751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81705, d82751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81705, d82751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81706 q = 1) (hb : d82752 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81706, d82752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81706, d82752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d81707 q = 1) (hb : d82753 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81707, d82753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81707, d82753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d81708 q = 1) (hb : d82754 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81708, d82754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81708, d82754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81728 q = 1) (hb : d82761 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81728, d82761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81728, d82761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10945 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d81729 q = 1) (hb : d82762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81729, d82762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81729, d82762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d81730 q = 1) (hb : d82763 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81730, d82763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81730, d82763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d81731 q = 1) (hb : d82764 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81731, d82764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81731, d82764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d81732 q = 1) (hb : d82765 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81732, d82765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81732, d82765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d81733 q = 1) (hb : d82766 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81733, d82766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d81733, d82766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10947 (p : Pattern) (ha : d81739 p = 1) (hb : d82772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81734 q = 1) (hb : d82767 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81734, d82767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81734, d82767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10946 q ha hb
  have h2 (q : Pattern) (ha : d81735 q = 1) (hb : d82768 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81735, d82768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81735, d82768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81736 q = 1) (hb : d82769 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81736, d82769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81736, d82769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81737 q = 1) (hb : d82770 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81737, d82770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81737, d82770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81738 q = 1) (hb : d82771 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81738, d82771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81738, d82771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81739 q = 1) (hb : d82772 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81739, d82772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81739, d82772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10948 (p : Pattern) (ha : d6263 p = 1) (hb : d81760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6258 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8965 q ha hb
    | true =>
      simp only [d6258, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h5 (q : Pattern) (ha : d6259 q = 1) (hb : d81756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6259, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6260 q = 1) (hb : d81757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6260, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6261 q = 1) (hb : d81758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6261, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6262 q = 1) (hb : d81759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6262, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6263 q = 1) (hb : d81760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6263, d81760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6263, d81760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10949 (p : Pattern) (ha : d6272 p = 1) (hb : d81768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81755 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6258 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8965 q ha hb
    | true =>
      simp only [d6258, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h4 (q : Pattern) (ha : d6259 q = 1) (hb : d81756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6259, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6260 q = 1) (hb : d81757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6260, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6261 q = 1) (hb : d81758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6261, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6262 q = 1) (hb : d81759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d81763 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6267 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6267, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8967 q ha hb
    | true =>
      simp only [d6267, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h13 (q : Pattern) (ha : d6268 q = 1) (hb : d81764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6268, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6269 q = 1) (hb : d81765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6269, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6270 q = 1) (hb : d81766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, d81766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6270, d81766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6271 q = 1) (hb : d81767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, d81767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6271, d81767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6272 q = 1) (hb : d81768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6272, d81768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6272, d81768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10950 (p : Pattern) (ha : d81782 p = 1) (hb : d82777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81763 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6267 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6267, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8967 q ha hb
    | true =>
      simp only [d6267, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h3 (q : Pattern) (ha : d6268 q = 1) (hb : d81764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6268, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6269 q = 1) (hb : d81765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6269, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6270 q = 1) (hb : d81780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, d81780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6270, d81780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6271 q = 1) (hb : d81781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, d81781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6271, d81781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81782 q = 1) (hb : d82777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81782, d82777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81782, d82777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10951 (p : Pattern) (ha : d81806 p = 1) (hb : d82788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52930 q = 1) (hb : d82783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52930, d82783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9054 q hb ha
    | true =>
      simp only [d52930, d82783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro170 q hb ha
  have h3 (q : Pattern) (ha : d81802 q = 1) (hb : d82784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81802, d82784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81802, d82784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76116 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81803 q = 1) (hb : d82785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81803, d82785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81803, d82785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81804 q = 1) (hb : d82786 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81804, d82786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81804, d82786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81805 q = 1) (hb : d82787 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81805, d82787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81805, d82787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81806 q = 1) (hb : d82788 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81806, d82788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81806, d82788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10952 (p : Pattern) (ha : d81812 p = 1) (hb : d82794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6273 q = 1) (hb : d81769 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6273, d81769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10948 q ha hb
    | true =>
      simp only [d6273, d81769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10949 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81776 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6274 q = 1) (hb : d81777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6274, d81777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6274, d81777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81778 q = 1) (hb : d82775 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81778, d82775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81778, d82775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81779 q = 1) (hb : d82776 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81779, d82776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81779, d82776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81783 q = 1) (hb : d82778 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81783, d82778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81783, d82778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10950 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d81784 q = 1) (hb : d82779 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81784, d82779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81784, d82779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81785 q = 1) (hb : d82780 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81785, d82780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81785, d82780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d81786 q = 1) (hb : d82781 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81786, d82781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81786, d82781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d81787 q = 1) (hb : d82782 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81787, d82782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81787, d82782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81807 q = 1) (hb : d82789 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81807, d82789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81807, d82789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10951 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d81808 q = 1) (hb : d82790 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81808, d82790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81808, d82790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d81809 q = 1) (hb : d82791 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81809, d82791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81809, d82791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d81810 q = 1) (hb : d82792 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81810, d82792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81810, d82792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d81811 q = 1) (hb : d82793 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81811, d82793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81811, d82793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d81812 q = 1) (hb : d82794 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81812, d82794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d81812, d82794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10953 (p : Pattern) (ha : d81818 p = 1) (hb : d82800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81813 q = 1) (hb : d82795 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81813, d82795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81813, d82795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10952 q ha hb
  have h2 (q : Pattern) (ha : d81814 q = 1) (hb : d82796 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81814, d82796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81814, d82796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81815 q = 1) (hb : d82797 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81815, d82797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81815, d82797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81816 q = 1) (hb : d82798 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81816, d82798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81816, d82798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81817 q = 1) (hb : d82799 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81817, d82799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81817, d82799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81818 q = 1) (hb : d82800 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81818, d82800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81818, d82800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10954 (p : Pattern) (ha : d6409 p = 1) (hb : d81840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81835 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6404 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8984 q ha hb
    | true =>
      simp only [d6404, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h5 (q : Pattern) (ha : d6405 q = 1) (hb : d81836 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6405, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6406 q = 1) (hb : d81837 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6406, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6407 q = 1) (hb : d81838 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6407, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6408 q = 1) (hb : d81839 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6408, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6409 q = 1) (hb : d81840 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6409, d81840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6409, d81840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10955 (p : Pattern) (ha : d6418 p = 1) (hb : d81848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6404 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8984 q ha hb
    | true =>
      simp only [d6404, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h4 (q : Pattern) (ha : d6405 q = 1) (hb : d81836 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6405, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6406 q = 1) (hb : d81837 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6406, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6407 q = 1) (hb : d81838 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6407, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6408 q = 1) (hb : d81839 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d81843 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6413 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6413, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8986 q ha hb
    | true =>
      simp only [d6413, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h13 (q : Pattern) (ha : d6414 q = 1) (hb : d81844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6414, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6415 q = 1) (hb : d81845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6415, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6416 q = 1) (hb : d81846 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, d81846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6416, d81846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6417 q = 1) (hb : d81847 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, d81847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6417, d81847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6418 q = 1) (hb : d81848 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6418, d81848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6418, d81848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10956 (p : Pattern) (ha : d81862 p = 1) (hb : d82806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81843 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6413 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6413, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8986 q ha hb
    | true =>
      simp only [d6413, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h3 (q : Pattern) (ha : d6414 q = 1) (hb : d81844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6414, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6415 q = 1) (hb : d81845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6415, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6416 q = 1) (hb : d81860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, d81860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6416, d81860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6417 q = 1) (hb : d81861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, d81861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6417, d81861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81862 q = 1) (hb : d82806 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81862, d82806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81862, d82806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10957 (p : Pattern) (ha : d81886 p = 1) (hb : d82817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53245 q = 1) (hb : d82812 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53245, d82812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9061 q hb ha
    | true =>
      simp only [d53245, d82812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro228 q hb ha
  have h3 (q : Pattern) (ha : d81882 q = 1) (hb : d82813 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81882, d82813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81882, d82813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76251 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81883 q = 1) (hb : d82814 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81883, d82814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81883, d82814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81884 q = 1) (hb : d82815 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81884, d82815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81884, d82815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81885 q = 1) (hb : d82816 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81885, d82816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81885, d82816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81886 q = 1) (hb : d82817 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81886, d82817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81886, d82817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10958 (p : Pattern) (ha : d81892 p = 1) (hb : d82823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6419 q = 1) (hb : d81849 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6419, d81849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10954 q ha hb
    | true =>
      simp only [d6419, d81849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10955 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81856 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6420 q = 1) (hb : d81857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6420, d81857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6420, d81857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81858 q = 1) (hb : d82804 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81858, d82804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81858, d82804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81859 q = 1) (hb : d82805 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81859, d82805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81859, d82805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81863 q = 1) (hb : d82807 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81863, d82807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81863, d82807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10956 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d81864 q = 1) (hb : d82808 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81864, d82808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81864, d82808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81865 q = 1) (hb : d82809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81865, d82809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81865, d82809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d81866 q = 1) (hb : d82810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81866, d82810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81866, d82810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d81867 q = 1) (hb : d82811 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81867, d82811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81867, d82811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81887 q = 1) (hb : d82818 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81887, d82818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81887, d82818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10957 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d81888 q = 1) (hb : d82819 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81888, d82819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81888, d82819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d81889 q = 1) (hb : d82820 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81889, d82820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81889, d82820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d81890 q = 1) (hb : d82821 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81890, d82821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81890, d82821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d81891 q = 1) (hb : d82822 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81891, d82822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81891, d82822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d81892 q = 1) (hb : d82823 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81892, d82823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d81892, d82823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10959 (p : Pattern) (ha : d81898 p = 1) (hb : d82829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81893 q = 1) (hb : d82824 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81893, d82824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81893, d82824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10958 q ha hb
  have h2 (q : Pattern) (ha : d81894 q = 1) (hb : d82825 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81894, d82825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81894, d82825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81895 q = 1) (hb : d82826 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81895, d82826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81895, d82826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81896 q = 1) (hb : d82827 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81896, d82827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81896, d82827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81897 q = 1) (hb : d82828 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81897, d82828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81897, d82828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81898 q = 1) (hb : d82829 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81898, d82829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81898, d82829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10960 (p : Pattern) (ha : d6556 p = 1) (hb : d81921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81916 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6551 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9003 q ha hb
    | true =>
      simp only [d6551, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h5 (q : Pattern) (ha : d6552 q = 1) (hb : d81917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6552, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6553 q = 1) (hb : d81918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6553, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6554 q = 1) (hb : d81919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6554, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6555 q = 1) (hb : d81920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6555, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6556 q = 1) (hb : d81921 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6556, d81921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6556, d81921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10961 (p : Pattern) (ha : d6565 p = 1) (hb : d81929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6551 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9003 q ha hb
    | true =>
      simp only [d6551, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h4 (q : Pattern) (ha : d6552 q = 1) (hb : d81917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6552, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6553 q = 1) (hb : d81918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6553, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6554 q = 1) (hb : d81919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6554, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6555 q = 1) (hb : d81920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d81924 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6560 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6560, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9005 q ha hb
    | true =>
      simp only [d6560, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h13 (q : Pattern) (ha : d6561 q = 1) (hb : d81925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6561, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6562 q = 1) (hb : d81926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6562, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6563 q = 1) (hb : d81927 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, d81927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6563, d81927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6564 q = 1) (hb : d81928 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, d81928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6564, d81928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6565 q = 1) (hb : d81929 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6565, d81929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6565, d81929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10962 (p : Pattern) (ha : d81943 p = 1) (hb : d82836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6560 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6560, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9005 q ha hb
    | true =>
      simp only [d6560, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h3 (q : Pattern) (ha : d6561 q = 1) (hb : d81925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6561, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6562 q = 1) (hb : d81926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6562, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6563 q = 1) (hb : d81941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, d81941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6563, d81941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6564 q = 1) (hb : d81942 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, d81942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6564, d81942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81943 q = 1) (hb : d82836 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81943, d82836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81943, d82836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10963 (p : Pattern) (ha : d81967 p = 1) (hb : d82847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81962 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53562 q = 1) (hb : d82842 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53562, d82842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9068 q hb ha
    | true =>
      simp only [d53562, d82842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro287 q hb ha
  have h3 (q : Pattern) (ha : d81963 q = 1) (hb : d82843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d81963, d82843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81963, d82843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76387 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81964 q = 1) (hb : d82844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d81964, d82844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81964, d82844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81965 q = 1) (hb : d82845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d81965, d82845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81965, d82845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81966 q = 1) (hb : d82846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d81966, d82846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81966, d82846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81967 q = 1) (hb : d82847 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d81967, d82847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81967, d82847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10964 (p : Pattern) (ha : d81973 p = 1) (hb : d82853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6566 q = 1) (hb : d81930 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6566, d81930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10960 q ha hb
    | true =>
      simp only [d6566, d81930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10961 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81937 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6567 q = 1) (hb : d81938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6567, d81938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6567, d81938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d81939 q = 1) (hb : d82834 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81939, d82834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81939, d82834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d81940 q = 1) (hb : d82835 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81940, d82835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81940, d82835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81944 q = 1) (hb : d82837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81944, d82837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81944, d82837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10962 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d81945 q = 1) (hb : d82838 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81945, d82838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81945, d82838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81946 q = 1) (hb : d82839 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81946, d82839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81946, d82839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d81947 q = 1) (hb : d82840 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81947, d82840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81947, d82840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d81948 q = 1) (hb : d82841 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81948, d82841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81948, d82841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81968 q = 1) (hb : d82848 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d81968, d82848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81968, d82848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10963 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d81969 q = 1) (hb : d82849 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d81969, d82849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d81969, d82849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d81970 q = 1) (hb : d82850 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d81970, d82850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81970, d82850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d81971 q = 1) (hb : d82851 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d81971, d82851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d81971, d82851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d81972 q = 1) (hb : d82852 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d81972, d82852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d81972, d82852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d81973 q = 1) (hb : d82853 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d81973, d82853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d81973, d82853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10965 (p : Pattern) (ha : d81979 p = 1) (hb : d82859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81974 q = 1) (hb : d82854 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d81974, d82854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81974, d82854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10964 q ha hb
  have h2 (q : Pattern) (ha : d81975 q = 1) (hb : d82855 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d81975, d82855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81975, d82855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81976 q = 1) (hb : d82856 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d81976, d82856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81976, d82856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81977 q = 1) (hb : d82857 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d81977, d82857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81977, d82857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81978 q = 1) (hb : d82858 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d81978, d82858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81978, d82858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81979 q = 1) (hb : d82859 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d81979, d82859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81979, d82859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10966 (p : Pattern) (ha : d81985 p = 1) (hb : d82865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d81662 q = 1) (hb : d82746 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81662, d82746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10935 q ha hb
    | true =>
      simp only [d81662, d82746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10941 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d81740 q = 1) (hb : d82773 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81740, d82773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81740, d82773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10947 q ha hb
  have h3 (q : Pattern) (ha : d81741 q = 1) (hb : d82774 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d81741, d82774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d81741, d82774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81819 q = 1) (hb : d82801 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81819, d82801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81819, d82801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10953 q ha hb
  have h5 (q : Pattern) (ha : d81820 q = 1) (hb : d82802 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d81820, d82802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81820, d82802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d81821 q = 1) (hb : d82803 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d81821, d82803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81821, d82803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d81899 q = 1) (hb : d82830 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81899, d82830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81899, d82830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10959 q ha hb
  have h8 (q : Pattern) (ha : d81900 q = 1) (hb : d82831 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d81900, d82831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81900, d82831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d81901 q = 1) (hb : d82832 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d81901, d82832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81901, d82832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81902 q = 1) (hb : d82833 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d81902, d82833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d81902, d82833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d81980 q = 1) (hb : d82860 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d81980, d82860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81980, d82860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10965 q ha hb
  have h12 (q : Pattern) (ha : d81981 q = 1) (hb : d82861 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d81981, d82861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81981, d82861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d81982 q = 1) (hb : d82862 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d81982, d82862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81982, d82862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d81983 q = 1) (hb : d82863 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d81983, d82863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d81983, d82863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d81984 q = 1) (hb : d82864 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d81984, d82864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81984, d82864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d81985 q = 1) (hb : d82865 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d81985, d82865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d81985, d82865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro10967 (p : Pattern) (ha : d81991 p = 1) (hb : d82871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81986 q = 1) (hb : d82866 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d81986, d82866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10966 q ha hb
    | true =>
      simp only [d81986, d82866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81987 q = 1) (hb : d82867 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d81987, d82867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d81987, d82867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d81988 q = 1) (hb : d82868 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d81988, d82868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d81988, d82868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81989 q = 1) (hb : d82869 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d81989, d82869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81989, d82869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d81990 q = 1) (hb : d82870 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d81990, d82870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81990, d82870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d81991 q = 1) (hb : d82871 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d81991, d82871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d81991, d82871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10968 (p : Pattern) (ha : d81997 p = 1) (hb : d82877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81992 q = 1) (hb : d82872 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d81992, d82872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10967 q ha hb
    | true =>
      simp only [d81992, d82872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81993 q = 1) (hb : d82873 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d81993, d82873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d81993, d82873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d81994 q = 1) (hb : d82874 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d81994, d82874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d81994, d82874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81995 q = 1) (hb : d82875 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d81995, d82875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81995, d82875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d81996 q = 1) (hb : d82876 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d81996, d82876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81996, d82876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d81997 q = 1) (hb : d82877 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d81997, d82877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d81997, d82877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10969 (p : Pattern) (ha : d82003 p = 1) (hb : d82883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81998 q = 1) (hb : d82878 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d81998, d82878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10968 q ha hb
    | true =>
      simp only [d81998, d82878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81999 q = 1) (hb : d82879 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d81999, d82879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d81999, d82879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82000 q = 1) (hb : d82880 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82000, d82880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82000, d82880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82001 q = 1) (hb : d82881 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82001, d82881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82001, d82881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82002 q = 1) (hb : d82882 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82002, d82882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82002, d82882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82003 q = 1) (hb : d82883 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82003, d82883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82003, d82883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10970 (p : Pattern) (ha : d82009 p = 1) (hb : d82889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82004 q = 1) (hb : d82884 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82004, d82884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10969 q ha hb
    | true =>
      simp only [d82004, d82884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d82005 q = 1) (hb : d82885 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82005, d82885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82005, d82885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82006 q = 1) (hb : d82886 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82006, d82886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82006, d82886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82007 q = 1) (hb : d82887 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82007, d82887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82007, d82887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82008 q = 1) (hb : d82888 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82008, d82888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82008, d82888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82009 q = 1) (hb : d82889 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82009, d82889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82009, d82889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10971 (p : Pattern) (ha : d82015 p = 1) (hb : d82895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82010 q = 1) (hb : d82890 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82010, d82890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10970 q ha hb
    | true =>
      simp only [d82010, d82890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d82011 q = 1) (hb : d82891 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82011, d82891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82011, d82891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82012 q = 1) (hb : d82892 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82012, d82892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82012, d82892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82013 q = 1) (hb : d82893 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82013, d82893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82013, d82893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82014 q = 1) (hb : d82894 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82014, d82894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82014, d82894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82015 q = 1) (hb : d82895 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82015, d82895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82015, d82895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10972 (p : Pattern) (ha : d82021 p = 1) (hb : d82901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82016 q = 1) (hb : d82896 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82016, d82896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10971 q ha hb
    | true =>
      simp only [d82016, d82896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d82017 q = 1) (hb : d82897 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82017, d82897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82017, d82897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82018 q = 1) (hb : d82898 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82018, d82898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82018, d82898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82019 q = 1) (hb : d82899 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82019, d82899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82019, d82899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82020 q = 1) (hb : d82900 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82020, d82900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82020, d82900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82021 q = 1) (hb : d82901 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82021, d82901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82021, d82901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10973 (p : Pattern) (ha : d82027 p = 1) (hb : d82907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82022 q = 1) (hb : d82902 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82022, d82902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10972 q ha hb
    | true =>
      simp only [d82022, d82902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d82023 q = 1) (hb : d82903 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82023, d82903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82023, d82903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d82024 q = 1) (hb : d82904 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82024, d82904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82024, d82904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d82025 q = 1) (hb : d82905 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82025, d82905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82025, d82905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d82026 q = 1) (hb : d82906 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82026, d82906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82026, d82906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d82027 q = 1) (hb : d82907 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82027, d82907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82027, d82907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro10974 (p : Pattern) (ha : d5895 p = 1) (hb : d82032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6746 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5850 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5891 q = 1) (hb : d82028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d82028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5891, d82028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5892 q = 1) (hb : d82029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d82029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5892, d82029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5893 q = 1) (hb : d82030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d82030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5893, d82030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5894 q = 1) (hb : d82031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d82031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5894, d82031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5895 q = 1) (hb : d82032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5895, d82032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5895, d82032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10975 (p : Pattern) (ha : d5902 p = 1) (hb : d82037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6746 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5850 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5891 q = 1) (hb : d82028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d82028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5891, d82028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5892 q = 1) (hb : d82029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d82029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5892, d82029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5893 q = 1) (hb : d82030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d82030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5893, d82030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5894 q = 1) (hb : d82031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d82031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d82031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d380 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d5856 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5898 q = 1) (hb : d82033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d82033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5898, d82033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5899 q = 1) (hb : d82034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, d82034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5899, d82034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5900 q = 1) (hb : d82035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, d82035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5900, d82035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5901 q = 1) (hb : d82036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, d82036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5901, d82036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d5902 q = 1) (hb : d82037 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5902, d82037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5902, d82037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10976 (p : Pattern) (ha : d82044 p = 1) (hb : d82697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5856 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5898 q = 1) (hb : d82033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d82033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5898, d82033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5899 q = 1) (hb : d82034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, d82034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5899, d82034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5900 q = 1) (hb : d82042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, d82042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5900, d82042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5901 q = 1) (hb : d82043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, d82043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5901, d82043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82044 q = 1) (hb : d82697 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82044, d82697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82044, d82697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10977 (p : Pattern) (ha : d82054 p = 1) (hb : d82707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5874 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82050 q = 1) (hb : d82703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82050, d82703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82050, d82703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82051 q = 1) (hb : d82704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82051, d82704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82051, d82704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82052 q = 1) (hb : d82705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82052, d82705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82052, d82705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82053 q = 1) (hb : d82706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82053, d82706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82053, d82706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82054 q = 1) (hb : d82707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82054, d82707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82054, d82707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10978 (p : Pattern) (ha : d82060 p = 1) (hb : d82713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5903 q = 1) (hb : d82038 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5903, d82038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10974 q ha hb
    | true =>
      simp only [d5903, d82038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10975 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5904 q = 1) (hb : d82039 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5904, d82039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5904, d82039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82040 q = 1) (hb : d82695 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82040, d82695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82040, d82695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82041 q = 1) (hb : d82696 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82041, d82696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82041, d82696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82045 q = 1) (hb : d82698 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82045, d82698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82045, d82698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10976 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82046 q = 1) (hb : d82699 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82046, d82699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82046, d82699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82047 q = 1) (hb : d82700 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82047, d82700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82047, d82700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82048 q = 1) (hb : d82701 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82048, d82701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82048, d82701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82049 q = 1) (hb : d82702 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82049, d82702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82049, d82702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82055 q = 1) (hb : d82708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82055, d82708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82055, d82708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10977 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82056 q = 1) (hb : d82709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82056, d82709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82056, d82709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82057 q = 1) (hb : d82710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82057, d82710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82057, d82710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82058 q = 1) (hb : d82711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82058, d82711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82058, d82711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82059 q = 1) (hb : d82712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82059, d82712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82059, d82712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82060 q = 1) (hb : d82713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82060, d82713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82060, d82713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10979 (p : Pattern) (ha : d82066 p = 1) (hb : d82719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro376 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82061 q = 1) (hb : d82714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82061, d82714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82061, d82714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10978 q ha hb
  have h8 (q : Pattern) (ha : d82062 q = 1) (hb : d82715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82062, d82715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82062, d82715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82063 q = 1) (hb : d82716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82063, d82716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82063, d82716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82064 q = 1) (hb : d82717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82064, d82717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82064, d82717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82065 q = 1) (hb : d82718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82065, d82718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82065, d82718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d82066 q = 1) (hb : d82719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82066, d82719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82066, d82719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro10980 (p : Pattern) (ha : d5997 p = 1) (hb : d82071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6810 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5992 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5993 q = 1) (hb : d82067 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d82067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5993, d82067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5994 q = 1) (hb : d82068 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d82068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5994, d82068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5995 q = 1) (hb : d82069 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d82069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5995, d82069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5996 q = 1) (hb : d82070 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d82070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5996, d82070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5997 q = 1) (hb : d82071 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5997, d82071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5997, d82071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10981 (p : Pattern) (ha : d6005 p = 1) (hb : d82076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6810 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5992 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5993 q = 1) (hb : d82067 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d82067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5993, d82067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5994 q = 1) (hb : d82068 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d82068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5994, d82068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5995 q = 1) (hb : d82069 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d82069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5995, d82069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5996 q = 1) (hb : d82070 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d82070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, d82070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d614 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d619 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6818 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6000 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d6001 q = 1) (hb : d82072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d82072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6001, d82072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6002 q = 1) (hb : d82073 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, d82073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6002, d82073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6003 q = 1) (hb : d82074 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, d82074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6003, d82074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6004 q = 1) (hb : d82075 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, d82075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6004, d82075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6005 q = 1) (hb : d82076 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6005, d82076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6005, d82076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10982 (p : Pattern) (ha : d82083 p = 1) (hb : d82722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6818 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6000 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6001 q = 1) (hb : d82072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d82072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6001, d82072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6002 q = 1) (hb : d82073 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, d82073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6002, d82073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6003 q = 1) (hb : d82081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, d82081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6003, d82081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6004 q = 1) (hb : d82082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, d82082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6004, d82082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82083 q = 1) (hb : d82722 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82083, d82722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82083, d82722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10983 (p : Pattern) (ha : d82093 p = 1) (hb : d82733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6856 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d82728 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82089 q = 1) (hb : d82729 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82089, d82729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82089, d82729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5430 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82090 q = 1) (hb : d82730 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82090, d82730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82090, d82730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82091 q = 1) (hb : d82731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82091, d82731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82091, d82731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82092 q = 1) (hb : d82732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82092, d82732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82092, d82732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82093 q = 1) (hb : d82733 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82093, d82733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82093, d82733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10984 (p : Pattern) (ha : d82099 p = 1) (hb : d82739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6006 q = 1) (hb : d82077 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6006, d82077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10980 q ha hb
    | true =>
      simp only [d6006, d82077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10981 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6831 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6007 q = 1) (hb : d82078 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6007, d82078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6007, d82078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82079 q = 1) (hb : d82720 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82079, d82720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82079, d82720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82080 q = 1) (hb : d82721 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82080, d82721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82080, d82721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82084 q = 1) (hb : d82723 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82084, d82723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82084, d82723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10982 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82085 q = 1) (hb : d82724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82085, d82724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82085, d82724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82086 q = 1) (hb : d82725 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82086, d82725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82086, d82725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82087 q = 1) (hb : d82726 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82087, d82726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82087, d82726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82088 q = 1) (hb : d82727 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82088, d82727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82088, d82727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82094 q = 1) (hb : d82734 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82094, d82734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82094, d82734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10983 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82095 q = 1) (hb : d82735 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82095, d82735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82095, d82735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82096 q = 1) (hb : d82736 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82096, d82736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82096, d82736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82097 q = 1) (hb : d82737 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82097, d82737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82097, d82737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82098 q = 1) (hb : d82738 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82098, d82738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82098, d82738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82099 q = 1) (hb : d82739 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82099, d82739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82099, d82739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10985 (p : Pattern) (ha : d82105 p = 1) (hb : d82745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82100 q = 1) (hb : d82740 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82100, d82740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82100, d82740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10984 q ha hb
  have h2 (q : Pattern) (ha : d82101 q = 1) (hb : d82741 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82101, d82741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82101, d82741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82102 q = 1) (hb : d82742 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82102, d82742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82102, d82742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82103 q = 1) (hb : d82743 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82103, d82743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82103, d82743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82104 q = 1) (hb : d82744 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82104, d82744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82104, d82744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82105 q = 1) (hb : d82745 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82105, d82745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82105, d82745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10986 (p : Pattern) (ha : d6124 p = 1) (hb : d82111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6888 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6120 q = 1) (hb : d82107 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6120, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6121 q = 1) (hb : d82108 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6121, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6122 q = 1) (hb : d82109 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6122, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6123 q = 1) (hb : d82110 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6123, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6124 q = 1) (hb : d82111 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6124, d82111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6124, d82111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10987 (p : Pattern) (ha : d6133 p = 1) (hb : d82116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6888 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6119 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6120 q = 1) (hb : d82107 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6120, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6161 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6121 q = 1) (hb : d82108 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6121, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6122 q = 1) (hb : d82109 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6122, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6123 q = 1) (hb : d82110 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d920 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d925 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6896 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6128 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d6129 q = 1) (hb : d82112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6129, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6182 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6130 q = 1) (hb : d82113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6130, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6131 q = 1) (hb : d82114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, d82114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6131, d82114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6132 q = 1) (hb : d82115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, d82115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6132, d82115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6133 q = 1) (hb : d82116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6133, d82116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6133, d82116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10988 (p : Pattern) (ha : d82123 p = 1) (hb : d82749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6896 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6129 q = 1) (hb : d82112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6129, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6182 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6130 q = 1) (hb : d82113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6130, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6131 q = 1) (hb : d82121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, d82121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6131, d82121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6132 q = 1) (hb : d82122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, d82122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6132, d82122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82123 q = 1) (hb : d82749 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82123, d82749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82123, d82749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10989 (p : Pattern) (ha : d82133 p = 1) (hb : d82760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d82755 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82129 q = 1) (hb : d82756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82129, d82756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82129, d82756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82130 q = 1) (hb : d82757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82130, d82757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82130, d82757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82131 q = 1) (hb : d82758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82131, d82758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82131, d82758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82132 q = 1) (hb : d82759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82132, d82759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82132, d82759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82133 q = 1) (hb : d82760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82133, d82760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82133, d82760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10990 (p : Pattern) (ha : d82139 p = 1) (hb : d82766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6134 q = 1) (hb : d82117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6134, d82117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10986 q ha hb
    | true =>
      simp only [d6134, d82117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10987 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6909 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6135 q = 1) (hb : d82118 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6135, d82118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6135, d82118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82119 q = 1) (hb : d82747 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82119, d82747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82119, d82747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82120 q = 1) (hb : d82748 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82120, d82748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82120, d82748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82124 q = 1) (hb : d82750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82124, d82750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82124, d82750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10988 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82125 q = 1) (hb : d82751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82125, d82751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82125, d82751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82126 q = 1) (hb : d82752 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82126, d82752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82126, d82752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82127 q = 1) (hb : d82753 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82127, d82753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82127, d82753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82128 q = 1) (hb : d82754 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82128, d82754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82128, d82754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82134 q = 1) (hb : d82761 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82134, d82761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82134, d82761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10989 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82135 q = 1) (hb : d82762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82135, d82762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82135, d82762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82136 q = 1) (hb : d82763 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82136, d82763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82136, d82763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82137 q = 1) (hb : d82764 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82137, d82764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82137, d82764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82138 q = 1) (hb : d82765 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82138, d82765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82138, d82765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82139 q = 1) (hb : d82766 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82139, d82766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82139, d82766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10991 (p : Pattern) (ha : d82145 p = 1) (hb : d82772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82140 q = 1) (hb : d82767 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82140, d82767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82140, d82767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10990 q ha hb
  have h2 (q : Pattern) (ha : d82141 q = 1) (hb : d82768 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82141, d82768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82141, d82768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82142 q = 1) (hb : d82769 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82142, d82769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82142, d82769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82143 q = 1) (hb : d82770 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82143, d82770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82143, d82770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82144 q = 1) (hb : d82771 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82144, d82771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82144, d82771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82145 q = 1) (hb : d82772 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82145, d82772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82145, d82772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10992 (p : Pattern) (ha : d6263 p = 1) (hb : d82152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6967 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6258 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6259 q = 1) (hb : d82148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6259, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6300 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6260 q = 1) (hb : d82149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6260, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6261 q = 1) (hb : d82150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6261, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6262 q = 1) (hb : d82151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6262, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6263 q = 1) (hb : d82152 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6263, d82152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6263, d82152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10993 (p : Pattern) (ha : d6272 p = 1) (hb : d82157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6967 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6258 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6259 q = 1) (hb : d82148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6259, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6300 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6260 q = 1) (hb : d82149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6260, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6261 q = 1) (hb : d82150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6261, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6262 q = 1) (hb : d82151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1331 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1336 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6975 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6267 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d6268 q = 1) (hb : d82153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6268, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6321 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6269 q = 1) (hb : d82154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6269, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6270 q = 1) (hb : d82155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, d82155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6270, d82155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6271 q = 1) (hb : d82156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, d82156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6271, d82156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6272 q = 1) (hb : d82157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6272, d82157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6272, d82157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro10994 (p : Pattern) (ha : d82164 p = 1) (hb : d82777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6975 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6267 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6268 q = 1) (hb : d82153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6268, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6321 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6269 q = 1) (hb : d82154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6269, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6270 q = 1) (hb : d82162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, d82162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6270, d82162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6271 q = 1) (hb : d82163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, d82163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6271, d82163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82164 q = 1) (hb : d82777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82164, d82777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82164, d82777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro10995 (p : Pattern) (ha : d82174 p = 1) (hb : d82788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d82783 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82170 q = 1) (hb : d82784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82170, d82784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82170, d82784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6380 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82171 q = 1) (hb : d82785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82171, d82785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82171, d82785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82172 q = 1) (hb : d82786 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82172, d82786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82172, d82786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82173 q = 1) (hb : d82787 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82173, d82787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82173, d82787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82174 q = 1) (hb : d82788 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82174, d82788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82174, d82788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10996 (p : Pattern) (ha : d82180 p = 1) (hb : d82794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6273 q = 1) (hb : d82158 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6273, d82158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10992 q ha hb
    | true =>
      simp only [d6273, d82158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10993 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6274 q = 1) (hb : d82159 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6274, d82159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6274, d82159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82160 q = 1) (hb : d82775 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82160, d82775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82160, d82775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82161 q = 1) (hb : d82776 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82161, d82776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82161, d82776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82165 q = 1) (hb : d82778 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82165, d82778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82165, d82778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10994 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82166 q = 1) (hb : d82779 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82166, d82779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82166, d82779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82167 q = 1) (hb : d82780 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82167, d82780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82167, d82780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82168 q = 1) (hb : d82781 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82168, d82781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82168, d82781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82169 q = 1) (hb : d82782 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82169, d82782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82169, d82782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82175 q = 1) (hb : d82789 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82175, d82789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82175, d82789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10995 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82176 q = 1) (hb : d82790 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82176, d82790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82176, d82790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82177 q = 1) (hb : d82791 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82177, d82791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82177, d82791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82178 q = 1) (hb : d82792 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82178, d82792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82178, d82792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82179 q = 1) (hb : d82793 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82179, d82793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82179, d82793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82180 q = 1) (hb : d82794 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82180, d82794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82180, d82794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10997 (p : Pattern) (ha : d82186 p = 1) (hb : d82800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82181 q = 1) (hb : d82795 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82181, d82795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82181, d82795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10996 q ha hb
  have h2 (q : Pattern) (ha : d82182 q = 1) (hb : d82796 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82182, d82796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82182, d82796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82183 q = 1) (hb : d82797 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82183, d82797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82183, d82797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82184 q = 1) (hb : d82798 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82184, d82798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82184, d82798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82185 q = 1) (hb : d82799 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82185, d82799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82185, d82799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82186 q = 1) (hb : d82800 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82186, d82800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82186, d82800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10998 (p : Pattern) (ha : d6409 p = 1) (hb : d82194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7047 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6404 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6405 q = 1) (hb : d82190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6405, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6446 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6406 q = 1) (hb : d82191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6406, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6407 q = 1) (hb : d82192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6407, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6408 q = 1) (hb : d82193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6408, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6409 q = 1) (hb : d82194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6409, d82194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6409, d82194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10999 (p : Pattern) (ha : d6418 p = 1) (hb : d82199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7047 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6404 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6405 q = 1) (hb : d82190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6405, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6446 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6406 q = 1) (hb : d82191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6406, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6407 q = 1) (hb : d82192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6407, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6408 q = 1) (hb : d82193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7055 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6413 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d6414 q = 1) (hb : d82195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6414, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6467 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6415 q = 1) (hb : d82196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6415, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6416 q = 1) (hb : d82197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, d82197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6416, d82197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6417 q = 1) (hb : d82198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, d82198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6417, d82198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6418 q = 1) (hb : d82199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6418, d82199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6418, d82199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
end NetHack.Soko22Hazard87
