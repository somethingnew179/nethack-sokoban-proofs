import NetHack.Soko22Hazard87.AndIntroBlocks0021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro5500 (p : Pattern) (ha : d52215 p = 1) (hb : d61555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52090 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
    | true =>
      simp only [d3343, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3345 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3345, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3345, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52162 q = 1) (hb : d61550 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52162, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54 q hb ha
    | true =>
      simp only [d52162, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51963 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3347 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3347, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38 q ha hb
    | true =>
      simp only [d3347, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52165 q = 1) (hb : d61551 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52165, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52165, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d52166 q = 1) (hb : d61552 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52166, d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d52167 q = 1) (hb : d61553 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52167, d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52176 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d52177 q = 1) (hb : d61554 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52177, d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52177, d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d52214 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d52215 q = 1) (hb : d61555 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52215, d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d52215, d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro5501 (p : Pattern) (ha : d52221 p = 1) (hb : d61561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3325 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3325, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3325, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5367 q ha hb
  have h2 (q : Pattern) (ha : d3326 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3326, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3326, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3327 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3327, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3327, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3328 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3328, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3328, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52074 q = 1) (hb : d61545 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52074, d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5499 q ha hb
  have h6 (q : Pattern) (ha : d52075 q = 1) (hb : d61546 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52075, d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52076 q = 1) (hb : d61547 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52076, d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52077 q = 1) (hb : d61548 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52077, d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52078 q = 1) (hb : d61549 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52078, d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52216 q = 1) (hb : d61556 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52216, d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52216, d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5500 q ha hb
  have h11 (q : Pattern) (ha : d52217 q = 1) (hb : d61557 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52217, d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52217, d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52218 q = 1) (hb : d61558 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52218, d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52218, d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d52219 q = 1) (hb : d61559 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52219, d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52219, d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d52220 q = 1) (hb : d61560 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52220, d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52220, d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52221 q = 1) (hb : d61561 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52221, d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52221, d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5502 (p : Pattern) (ha : d52419 p = 1) (hb : d61567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52254 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
    | true =>
      simp only [d3359, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3361 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3361, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3361, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52335 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52336 q = 1) (hb : d61562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52336, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92 q hb ha
    | true =>
      simp only [d52336, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52348 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3363 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3363, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68 q ha hb
    | true =>
      simp only [d3363, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52350 q = 1) (hb : d61563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52350, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52350, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d52351 q = 1) (hb : d61564 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52351, d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d52352 q = 1) (hb : d61565 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52352, d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52361 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d52362 q = 1) (hb : d61566 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52362, d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52362, d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d52418 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d52419 q = 1) (hb : d61567 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52419, d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d52419, d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro5503 (p : Pattern) (ha : d52425 p = 1) (hb : d61573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52420 q = 1) (hb : d61568 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52420, d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52420, d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5502 q ha hb
  have h2 (q : Pattern) (ha : d52421 q = 1) (hb : d61569 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52421, d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52421, d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52422 q = 1) (hb : d61570 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52422, d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52422, d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52423 q = 1) (hb : d61571 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52423, d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52423, d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52424 q = 1) (hb : d61572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52424, d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52424, d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52425 q = 1) (hb : d61573 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52425, d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52425, d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5504 (p : Pattern) (ha : d52656 p = 1) (hb : d61580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52476 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d3376, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3378 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3378, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3378, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52557 q = 1) (hb : d61575 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52557, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro139 q hb ha
    | true =>
      simp only [d52557, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52569 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3380 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3380, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro112 q ha hb
    | true =>
      simp only [d3380, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52571 q = 1) (hb : d61576 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52571, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52571, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d52572 q = 1) (hb : d61577 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52572, d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d52573 q = 1) (hb : d61578 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52573, d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52582 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d52583 q = 1) (hb : d61579 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52583, d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52583, d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d52655 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d52656 q = 1) (hb : d61580 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52656, d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d52656, d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro5505 (p : Pattern) (ha : d52662 p = 1) (hb : d61586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52657 q = 1) (hb : d61581 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52657, d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52657, d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5504 q ha hb
  have h2 (q : Pattern) (ha : d52658 q = 1) (hb : d61582 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52658, d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52658, d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52659 q = 1) (hb : d61583 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52659, d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52659, d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52660 q = 1) (hb : d61584 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52660, d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52660, d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52661 q = 1) (hb : d61585 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52661, d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52661, d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52662 q = 1) (hb : d61586 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52662, d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52662, d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5506 (p : Pattern) (ha : d52950 p = 1) (hb : d61594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52759 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d3394, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3396 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3396, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3396, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52836 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52837 q = 1) (hb : d61589 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52837, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro191 q hb ha
    | true =>
      simp only [d52837, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52849 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3398 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3398, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro164 q ha hb
    | true =>
      simp only [d3398, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52851 q = 1) (hb : d61590 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52851, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52851, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d52852 q = 1) (hb : d61591 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52852, d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d52853 q = 1) (hb : d61592 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52853, d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52862 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d52863 q = 1) (hb : d61593 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52863, d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52863, d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d52949 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d52950 q = 1) (hb : d61594 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52950, d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d52950, d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro5507 (p : Pattern) (ha : d52956 p = 1) (hb : d61600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52951 q = 1) (hb : d61595 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52951, d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52951, d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5506 q ha hb
  have h2 (q : Pattern) (ha : d52952 q = 1) (hb : d61596 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52952, d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52952, d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52953 q = 1) (hb : d61597 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52953, d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52953, d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52954 q = 1) (hb : d61598 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52954, d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52954, d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52955 q = 1) (hb : d61599 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52955, d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52955, d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52956 q = 1) (hb : d61600 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52956, d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52956, d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5508 (p : Pattern) (ha : d53265 p = 1) (hb : d61609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53080 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d3413, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3415 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3415, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3415, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53151 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53152 q = 1) (hb : d61604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53152, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro247 q hb ha
    | true =>
      simp only [d53152, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53164 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3417 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3417, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro222 q ha hb
    | true =>
      simp only [d3417, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53166 q = 1) (hb : d61605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53166, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53166, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53167 q = 1) (hb : d61606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53167, d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d53168 q = 1) (hb : d61607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53168, d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53177 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d53178 q = 1) (hb : d61608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53178, d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53178, d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53264 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d53265 q = 1) (hb : d61609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53265, d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53265, d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro5509 (p : Pattern) (ha : d53271 p = 1) (hb : d61615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53266 q = 1) (hb : d61610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53266, d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53266, d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5508 q ha hb
  have h2 (q : Pattern) (ha : d53267 q = 1) (hb : d61611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53267, d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53267, d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53268 q = 1) (hb : d61612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53268, d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53268, d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53269 q = 1) (hb : d61613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53269, d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53269, d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53270 q = 1) (hb : d61614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53270, d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53270, d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53271 q = 1) (hb : d61615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53271, d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53271, d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5510 (p : Pattern) (ha : d53582 p = 1) (hb : d61625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d3433, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3435 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3435, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3435, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53468 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53469 q = 1) (hb : d61620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53469, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro306 q hb ha
    | true =>
      simp only [d53469, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53481 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3437 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3437, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro281 q ha hb
    | true =>
      simp only [d3437, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53483 q = 1) (hb : d61621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53483, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53483, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53484 q = 1) (hb : d61622 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53484, d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d53485 q = 1) (hb : d61623 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53485, d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53494 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d53495 q = 1) (hb : d61624 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53495, d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53495, d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53581 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d53582 q = 1) (hb : d61625 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53582, d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53582, d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro5511 (p : Pattern) (ha : d53588 p = 1) (hb : d61631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53583 q = 1) (hb : d61626 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53583, d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53583, d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5510 q ha hb
  have h2 (q : Pattern) (ha : d53584 q = 1) (hb : d61627 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53584, d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53584, d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53585 q = 1) (hb : d61628 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53585, d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53585, d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53586 q = 1) (hb : d61629 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53586, d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53586, d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53587 q = 1) (hb : d61630 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53587, d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53587, d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53588 q = 1) (hb : d61631 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53588, d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53588, d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5512 (p : Pattern) (ha : d53594 p = 1) (hb : d61637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d52426 q = 1) (hb : d61574 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d52426, d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5501 q ha hb
    | true =>
      simp only [d52426, d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5503 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52663 q = 1) (hb : d61587 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d52663, d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52663, d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5505 q ha hb
  have h3 (q : Pattern) (ha : d52664 q = 1) (hb : d61588 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d52664, d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d52664, d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52957 q = 1) (hb : d61601 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d52957, d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52957, d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5507 q ha hb
  have h5 (q : Pattern) (ha : d52958 q = 1) (hb : d61602 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d52958, d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52958, d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52959 q = 1) (hb : d61603 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d52959, d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52959, d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53272 q = 1) (hb : d61616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53272, d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53272, d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5509 q ha hb
  have h8 (q : Pattern) (ha : d53273 q = 1) (hb : d61617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53273, d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53273, d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53274 q = 1) (hb : d61618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53274, d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53274, d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53275 q = 1) (hb : d61619 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53275, d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53275, d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53589 q = 1) (hb : d61632 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53589, d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53589, d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5511 q ha hb
  have h12 (q : Pattern) (ha : d53590 q = 1) (hb : d61633 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53590, d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53590, d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53591 q = 1) (hb : d61634 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53591, d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53591, d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53592 q = 1) (hb : d61635 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53592, d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53592, d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53593 q = 1) (hb : d61636 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53593, d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53593, d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53594 q = 1) (hb : d61637 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53594, d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53594, d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5513 (p : Pattern) (ha : d53600 p = 1) (hb : d61643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53595 q = 1) (hb : d61638 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53595, d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5512 q ha hb
    | true =>
      simp only [d53595, d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53596 q = 1) (hb : d61639 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53596, d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53596, d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53597 q = 1) (hb : d61640 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53597, d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53597, d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53598 q = 1) (hb : d61641 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53598, d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53598, d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53599 q = 1) (hb : d61642 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53599, d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53599, d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53600 q = 1) (hb : d61643 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53600, d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53600, d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5514 (p : Pattern) (ha : d53606 p = 1) (hb : d61649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53601 q = 1) (hb : d61644 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53601, d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5513 q ha hb
    | true =>
      simp only [d53601, d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53602 q = 1) (hb : d61645 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53602, d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53602, d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53603 q = 1) (hb : d61646 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53603, d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53603, d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53604 q = 1) (hb : d61647 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53604, d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53604, d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53605 q = 1) (hb : d61648 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53605, d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53605, d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53606 q = 1) (hb : d61649 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53606, d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53606, d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5515 (p : Pattern) (ha : d53612 p = 1) (hb : d61655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53607 q = 1) (hb : d61650 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53607, d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5514 q ha hb
    | true =>
      simp only [d53607, d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53608 q = 1) (hb : d61651 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53608, d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53608, d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53609 q = 1) (hb : d61652 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53609, d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53609, d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53610 q = 1) (hb : d61653 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53610, d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53610, d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53611 q = 1) (hb : d61654 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53611, d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53611, d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53612 q = 1) (hb : d61655 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53612, d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53612, d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5516 (p : Pattern) (ha : d53618 p = 1) (hb : d61661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53613 q = 1) (hb : d61656 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53613, d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5515 q ha hb
    | true =>
      simp only [d53613, d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53614 q = 1) (hb : d61657 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53614, d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53614, d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53615 q = 1) (hb : d61658 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53615, d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53615, d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53616 q = 1) (hb : d61659 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53616, d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53616, d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53617 q = 1) (hb : d61660 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53617, d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53617, d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53618 q = 1) (hb : d61661 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53618, d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53618, d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5517 (p : Pattern) (ha : d53624 p = 1) (hb : d61667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53619 q = 1) (hb : d61662 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53619, d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5516 q ha hb
    | true =>
      simp only [d53619, d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53620 q = 1) (hb : d61663 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53620, d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53620, d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53621 q = 1) (hb : d61664 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53621, d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53621, d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53622 q = 1) (hb : d61665 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53622, d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53622, d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53623 q = 1) (hb : d61666 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53623, d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53623, d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53624 q = 1) (hb : d61667 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53624, d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53624, d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5518 (p : Pattern) (ha : d53630 p = 1) (hb : d61673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53625 q = 1) (hb : d61668 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53625, d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5517 q ha hb
    | true =>
      simp only [d53625, d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53626 q = 1) (hb : d61669 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53626, d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53626, d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53627 q = 1) (hb : d61670 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53627, d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53627, d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53628 q = 1) (hb : d61671 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53628, d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53628, d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53629 q = 1) (hb : d61672 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53629, d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53629, d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53630 q = 1) (hb : d61673 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53630, d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53630, d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5519 (p : Pattern) (ha : d53636 p = 1) (hb : d61679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53631 q = 1) (hb : d61674 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53631, d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5518 q ha hb
    | true =>
      simp only [d53631, d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53632 q = 1) (hb : d61675 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53632, d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53632, d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53633 q = 1) (hb : d61676 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53633, d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53633, d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53634 q = 1) (hb : d61677 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53634, d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53634, d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53635 q = 1) (hb : d61678 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53635, d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53635, d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53636 q = 1) (hb : d61679 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53636, d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53636, d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5520 (p : Pattern) (ha : d61360 p = 1) (hb : d61806 p = 1) : d61806 p = 1 := by
  have h0 (q : Pattern) (ha : d61360 q = 1) (hb : d61806 q = 1) : d61806 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro5521 (p : Pattern) (ha : d52073 p = 1) (hb : d61683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52029 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro323 q ha hb
    | true =>
      simp only [d3329, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52034 q = 1) (hb : d61680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52034, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52035 q = 1) (hb : d61681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52035, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52043 q = 1) (hb : d61682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52043, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52072 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52073 q = 1) (hb : d61683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52073, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52073, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5522 (p : Pattern) (ha : d52215 p = 1) (hb : d61692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52161 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro328 q ha hb
    | true =>
      simp only [d3343, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52166 q = 1) (hb : d61689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52166, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52167 q = 1) (hb : d61690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52167, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52176 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52177 q = 1) (hb : d61691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52177, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52177, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52214 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52215 q = 1) (hb : d61692 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52215, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52215, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5523 (p : Pattern) (ha : d52221 p = 1) (hb : d61698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52074 q = 1) (hb : d61684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52074, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5521 q ha hb
  have h3 (q : Pattern) (ha : d52075 q = 1) (hb : d61685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52075, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52076 q = 1) (hb : d61686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52076, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52077 q = 1) (hb : d61687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52077, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52078 q = 1) (hb : d61688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52078, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52216 q = 1) (hb : d61693 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52216, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52216, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5522 q ha hb
  have h8 (q : Pattern) (ha : d52217 q = 1) (hb : d61694 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52217, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52217, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52218 q = 1) (hb : d61695 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52218, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52218, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52219 q = 1) (hb : d61696 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52219, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52219, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52220 q = 1) (hb : d61697 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52220, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52220, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52221 q = 1) (hb : d61698 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52221, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52221, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5524 (p : Pattern) (ha : d52419 p = 1) (hb : d61702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro334 q ha hb
    | true =>
      simp only [d3359, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d52350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52351 q = 1) (hb : d61699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52351, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52352 q = 1) (hb : d61700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52352, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52361 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52362 q = 1) (hb : d61701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52362, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52362, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52418 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52419 q = 1) (hb : d61702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52419, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52419, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5525 (p : Pattern) (ha : d52425 p = 1) (hb : d61708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52420 q = 1) (hb : d61703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52420, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52420, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5524 q ha hb
  have h2 (q : Pattern) (ha : d52421 q = 1) (hb : d61704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52421, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52421, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52422 q = 1) (hb : d61705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52422, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52422, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52423 q = 1) (hb : d61706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52423, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52423, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52424 q = 1) (hb : d61707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52424, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52424, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52425 q = 1) (hb : d61708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52425, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52425, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5526 (p : Pattern) (ha : d52656 p = 1) (hb : d61713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro340 q ha hb
    | true =>
      simp only [d3376, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d52571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52572 q = 1) (hb : d61710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52572, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52573 q = 1) (hb : d61711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52573, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52582 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52583 q = 1) (hb : d61712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52583, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52583, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52655 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52656 q = 1) (hb : d61713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52656, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52656, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5527 (p : Pattern) (ha : d52662 p = 1) (hb : d61719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52657 q = 1) (hb : d61714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52657, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52657, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5526 q ha hb
  have h2 (q : Pattern) (ha : d52658 q = 1) (hb : d61715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52658, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52658, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52659 q = 1) (hb : d61716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52659, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52659, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52660 q = 1) (hb : d61717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52660, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52660, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52661 q = 1) (hb : d61718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52661, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52661, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52662 q = 1) (hb : d61719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52662, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52662, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5528 (p : Pattern) (ha : d52950 p = 1) (hb : d61725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro346 q ha hb
    | true =>
      simp only [d3394, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d52851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52852 q = 1) (hb : d61722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52852, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52853 q = 1) (hb : d61723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52853, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52862 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52863 q = 1) (hb : d61724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52863, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52863, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52949 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52950 q = 1) (hb : d61725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52950, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52950, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5529 (p : Pattern) (ha : d52956 p = 1) (hb : d61731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52951 q = 1) (hb : d61726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52951, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52951, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5528 q ha hb
  have h2 (q : Pattern) (ha : d52952 q = 1) (hb : d61727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52952, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52952, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52953 q = 1) (hb : d61728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52953, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52953, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52954 q = 1) (hb : d61729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52954, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52954, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52955 q = 1) (hb : d61730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52955, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52955, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52956 q = 1) (hb : d61731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52956, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52956, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5530 (p : Pattern) (ha : d53265 p = 1) (hb : d61738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53151 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro352 q ha hb
    | true =>
      simp only [d3413, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d53166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53167 q = 1) (hb : d61735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53167, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d53168 q = 1) (hb : d61736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53168, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53177 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53178 q = 1) (hb : d61737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53178, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53178, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53264 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53265 q = 1) (hb : d61738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53265, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53265, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5531 (p : Pattern) (ha : d53271 p = 1) (hb : d61744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53266 q = 1) (hb : d61739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53266, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53266, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5530 q ha hb
  have h2 (q : Pattern) (ha : d53267 q = 1) (hb : d61740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53267, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53267, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53268 q = 1) (hb : d61741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53268, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53268, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53269 q = 1) (hb : d61742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53269, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53269, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53270 q = 1) (hb : d61743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53270, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53270, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53271 q = 1) (hb : d61744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53271, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53271, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5532 (p : Pattern) (ha : d53582 p = 1) (hb : d61752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro358 q ha hb
    | true =>
      simp only [d3433, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d53483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53484 q = 1) (hb : d61749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53484, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d53485 q = 1) (hb : d61750 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53485, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53494 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53495 q = 1) (hb : d61751 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53495, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53495, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53581 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53582 q = 1) (hb : d61752 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53582, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53582, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5533 (p : Pattern) (ha : d53588 p = 1) (hb : d61758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53583 q = 1) (hb : d61753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53583, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53583, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5532 q ha hb
  have h2 (q : Pattern) (ha : d53584 q = 1) (hb : d61754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53584, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53584, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53585 q = 1) (hb : d61755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53585, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53585, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53586 q = 1) (hb : d61756 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53586, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53586, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53587 q = 1) (hb : d61757 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53587, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53587, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53588 q = 1) (hb : d61758 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53588, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53588, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5534 (p : Pattern) (ha : d53594 p = 1) (hb : d61764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d52426 q = 1) (hb : d61709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d52426, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5523 q ha hb
    | true =>
      simp only [d52426, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5525 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52663 q = 1) (hb : d61720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d52663, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52663, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5527 q ha hb
  have h3 (q : Pattern) (ha : d52664 q = 1) (hb : d61721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d52664, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d52664, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52957 q = 1) (hb : d61732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d52957, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52957, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5529 q ha hb
  have h5 (q : Pattern) (ha : d52958 q = 1) (hb : d61733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d52958, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52958, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52959 q = 1) (hb : d61734 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d52959, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52959, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53272 q = 1) (hb : d61745 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53272, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53272, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5531 q ha hb
  have h8 (q : Pattern) (ha : d53273 q = 1) (hb : d61746 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53273, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53273, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53274 q = 1) (hb : d61747 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53274, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53274, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53275 q = 1) (hb : d61748 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53275, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53275, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53589 q = 1) (hb : d61759 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53589, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53589, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5533 q ha hb
  have h12 (q : Pattern) (ha : d53590 q = 1) (hb : d61760 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53590, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53590, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53591 q = 1) (hb : d61761 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53591, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53591, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53592 q = 1) (hb : d61762 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53592, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53592, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53593 q = 1) (hb : d61763 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53593, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53593, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53594 q = 1) (hb : d61764 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53594, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53594, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5535 (p : Pattern) (ha : d53600 p = 1) (hb : d61770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53595 q = 1) (hb : d61765 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53595, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5534 q ha hb
    | true =>
      simp only [d53595, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53596 q = 1) (hb : d61766 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53596, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53596, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53597 q = 1) (hb : d61767 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53597, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53597, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53598 q = 1) (hb : d61768 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53598, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53598, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53599 q = 1) (hb : d61769 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53599, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53599, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53600 q = 1) (hb : d61770 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53600, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53600, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5536 (p : Pattern) (ha : d53606 p = 1) (hb : d61776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53601 q = 1) (hb : d61771 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53601, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5535 q ha hb
    | true =>
      simp only [d53601, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53602 q = 1) (hb : d61772 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53602, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53602, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53603 q = 1) (hb : d61773 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53603, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53603, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53604 q = 1) (hb : d61774 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53604, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53604, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53605 q = 1) (hb : d61775 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53605, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53605, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53606 q = 1) (hb : d61776 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53606, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53606, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5537 (p : Pattern) (ha : d53612 p = 1) (hb : d61782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53607 q = 1) (hb : d61777 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53607, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5536 q ha hb
    | true =>
      simp only [d53607, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53608 q = 1) (hb : d61778 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53608, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53608, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53609 q = 1) (hb : d61779 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53609, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53609, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53610 q = 1) (hb : d61780 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53610, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53610, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53611 q = 1) (hb : d61781 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53611, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53611, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53612 q = 1) (hb : d61782 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53612, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53612, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5538 (p : Pattern) (ha : d53618 p = 1) (hb : d61788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53613 q = 1) (hb : d61783 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53613, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5537 q ha hb
    | true =>
      simp only [d53613, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53614 q = 1) (hb : d61784 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53614, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53614, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53615 q = 1) (hb : d61785 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53615, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53615, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53616 q = 1) (hb : d61786 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53616, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53616, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53617 q = 1) (hb : d61787 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53617, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53617, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53618 q = 1) (hb : d61788 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53618, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53618, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5539 (p : Pattern) (ha : d53624 p = 1) (hb : d61794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53619 q = 1) (hb : d61789 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53619, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5538 q ha hb
    | true =>
      simp only [d53619, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53620 q = 1) (hb : d61790 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53620, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53620, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53621 q = 1) (hb : d61791 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53621, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53621, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53622 q = 1) (hb : d61792 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53622, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53622, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53623 q = 1) (hb : d61793 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53623, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53623, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53624 q = 1) (hb : d61794 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53624, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53624, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5540 (p : Pattern) (ha : d53630 p = 1) (hb : d61800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53625 q = 1) (hb : d61795 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53625, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5539 q ha hb
    | true =>
      simp only [d53625, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53626 q = 1) (hb : d61796 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53626, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53626, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53627 q = 1) (hb : d61797 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53627, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53627, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53628 q = 1) (hb : d61798 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53628, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53628, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53629 q = 1) (hb : d61799 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53629, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53629, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53630 q = 1) (hb : d61800 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53630, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53630, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5541 (p : Pattern) (ha : d53636 p = 1) (hb : d61806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53631 q = 1) (hb : d61801 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53631, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5540 q ha hb
    | true =>
      simp only [d53631, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53632 q = 1) (hb : d61802 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53632, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53632, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53633 q = 1) (hb : d61803 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53633, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53633, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53634 q = 1) (hb : d61804 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53634, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53634, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53635 q = 1) (hb : d61805 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53635, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53635, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53636 q = 1) (hb : d61806 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53636, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53636, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5542 (p : Pattern) (ha : d51652 p = 1) (hb : d61683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51646 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d51647 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro372 q ha hb
    | true =>
      simp only [d3329, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d51648 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51649 q = 1) (hb : d61680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51649, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51650 q = 1) (hb : d61681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51650, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d4353 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51651 q = 1) (hb : d61682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51651, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4364 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51652 q = 1) (hb : d61683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51652, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5543 (p : Pattern) (ha : d51676 p = 1) (hb : d61692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51663 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d51664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro377 q ha hb
    | true =>
      simp only [d3343, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d51665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d51665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d51665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51666 q = 1) (hb : d61689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51666, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51667 q = 1) (hb : d61690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51667, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51670 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51671 q = 1) (hb : d61691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51671, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51671, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51675 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51676 q = 1) (hb : d61692 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51676, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51676, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5544 (p : Pattern) (ha : d51682 p = 1) (hb : d61698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d61684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5542 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d61685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d61686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d61687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d61688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51657, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51677 q = 1) (hb : d61693 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51677, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51677, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5543 q ha hb
  have h8 (q : Pattern) (ha : d51678 q = 1) (hb : d61694 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51678, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51678, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51679 q = 1) (hb : d61695 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51679, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51679, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51680 q = 1) (hb : d61696 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51680, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51680, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51681 q = 1) (hb : d61697 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51681, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51681, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d51682 q = 1) (hb : d61698 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51682, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51682, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5545 (p : Pattern) (ha : d51701 p = 1) (hb : d61702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d51689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro383 q ha hb
    | true =>
      simp only [d3359, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d645 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d51690 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d51690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d51690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51691 q = 1) (hb : d61699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51691, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51692 q = 1) (hb : d61700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51692, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51695 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51696 q = 1) (hb : d61701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51696, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51696, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51700 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51701 q = 1) (hb : d61702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51701, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51701, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5546 (p : Pattern) (ha : d51707 p = 1) (hb : d61708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51702 q = 1) (hb : d61703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51702, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51702, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5545 q ha hb
  have h2 (q : Pattern) (ha : d51703 q = 1) (hb : d61704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51703, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51703, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51704 q = 1) (hb : d61705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51704, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51704, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51705 q = 1) (hb : d61706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51705, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51705, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51706 q = 1) (hb : d61707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51706, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51706, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51707 q = 1) (hb : d61708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51707, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51707, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5547 (p : Pattern) (ha : d51727 p = 1) (hb : d61713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51714 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d51715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro389 q ha hb
    | true =>
      simp only [d3376, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d951 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d51716 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51717 q = 1) (hb : d61710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51717, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51718 q = 1) (hb : d61711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51718, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51721 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51722 q = 1) (hb : d61712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51722, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51722, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51726 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51727 q = 1) (hb : d61713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51727, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51727, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5548 (p : Pattern) (ha : d51733 p = 1) (hb : d61719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51728 q = 1) (hb : d61714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51728, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51728, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5547 q ha hb
  have h2 (q : Pattern) (ha : d51729 q = 1) (hb : d61715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51729, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51729, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51730 q = 1) (hb : d61716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51730, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51730, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51731 q = 1) (hb : d61717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51731, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51731, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51732 q = 1) (hb : d61718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51732, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51732, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51733 q = 1) (hb : d61719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51733, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51733, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5549 (p : Pattern) (ha : d51754 p = 1) (hb : d61725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d51742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro395 q ha hb
    | true =>
      simp only [d3394, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1362 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d51743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51744 q = 1) (hb : d61722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51744, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51745 q = 1) (hb : d61723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51745, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51748 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51749 q = 1) (hb : d61724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51749, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51749, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51753 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51754 q = 1) (hb : d61725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51754, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51754, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5550 (p : Pattern) (ha : d51760 p = 1) (hb : d61731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51755 q = 1) (hb : d61726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51755, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51755, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5549 q ha hb
  have h2 (q : Pattern) (ha : d51756 q = 1) (hb : d61727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51756, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51756, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51757 q = 1) (hb : d61728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51757, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51757, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51758 q = 1) (hb : d61729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51758, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51758, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51759 q = 1) (hb : d61730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51759, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51759, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51760 q = 1) (hb : d61731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51760, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51760, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5551 (p : Pattern) (ha : d51782 p = 1) (hb : d61738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51769 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d51770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro401 q ha hb
    | true =>
      simp only [d3413, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1839 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d51771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d51771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d51771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51772 q = 1) (hb : d61735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51772, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51773 q = 1) (hb : d61736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51773, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51776 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51777 q = 1) (hb : d61737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51777, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51777, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51781 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51782 q = 1) (hb : d61738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51782, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51782, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5552 (p : Pattern) (ha : d51788 p = 1) (hb : d61744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51783 q = 1) (hb : d61739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51783, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51783, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5551 q ha hb
  have h2 (q : Pattern) (ha : d51784 q = 1) (hb : d61740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51784, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51784, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51785 q = 1) (hb : d61741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51785, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51785, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51786 q = 1) (hb : d61742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51786, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51786, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51787 q = 1) (hb : d61743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51787, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51787, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51788 q = 1) (hb : d61744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51788, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51788, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5553 (p : Pattern) (ha : d51811 p = 1) (hb : d61752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51798 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d51799 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro407 q ha hb
    | true =>
      simp only [d3433, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2317 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d51800 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d51800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d51800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51801 q = 1) (hb : d61749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51801, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51802 q = 1) (hb : d61750 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51802, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51805 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51806 q = 1) (hb : d61751 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51806, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51806, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51810 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51811 q = 1) (hb : d61752 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51811, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51811, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5554 (p : Pattern) (ha : d51817 p = 1) (hb : d61758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51812 q = 1) (hb : d61753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51812, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51812, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5553 q ha hb
  have h2 (q : Pattern) (ha : d51813 q = 1) (hb : d61754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51813, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51813, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51814 q = 1) (hb : d61755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51814, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51814, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51815 q = 1) (hb : d61756 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51815, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51815, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51816 q = 1) (hb : d61757 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51816, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51816, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51817 q = 1) (hb : d61758 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51817, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51817, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5555 (p : Pattern) (ha : d51823 p = 1) (hb : d61764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d51708 q = 1) (hb : d61709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51708, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5544 q ha hb
    | true =>
      simp only [d51708, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5546 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51734 q = 1) (hb : d61720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51734, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51734, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5548 q ha hb
  have h3 (q : Pattern) (ha : d51735 q = 1) (hb : d61721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51735, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51735, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51761 q = 1) (hb : d61732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51761, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51761, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5550 q ha hb
  have h5 (q : Pattern) (ha : d51762 q = 1) (hb : d61733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51762, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51762, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51763 q = 1) (hb : d61734 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51763, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51763, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51789 q = 1) (hb : d61745 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51789, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51789, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5552 q ha hb
  have h8 (q : Pattern) (ha : d51790 q = 1) (hb : d61746 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51790, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51790, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51791 q = 1) (hb : d61747 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51791, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51791, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51792 q = 1) (hb : d61748 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d51792, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51792, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51818 q = 1) (hb : d61759 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51818, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51818, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5554 q ha hb
  have h12 (q : Pattern) (ha : d51819 q = 1) (hb : d61760 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51819, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51819, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51820 q = 1) (hb : d61761 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51820, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51820, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51821 q = 1) (hb : d61762 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d51821, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51821, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51822 q = 1) (hb : d61763 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d51822, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51822, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51823 q = 1) (hb : d61764 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d51823, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d51823, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5556 (p : Pattern) (ha : d51829 p = 1) (hb : d61770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51824 q = 1) (hb : d61765 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d51824, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5555 q ha hb
    | true =>
      simp only [d51824, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51825 q = 1) (hb : d61766 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d51825, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51825, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51826 q = 1) (hb : d61767 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d51826, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51826, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51827 q = 1) (hb : d61768 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d51827, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51827, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51828 q = 1) (hb : d61769 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d51828, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51828, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51829 q = 1) (hb : d61770 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d51829, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51829, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5557 (p : Pattern) (ha : d51835 p = 1) (hb : d61776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51830 q = 1) (hb : d61771 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d51830, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5556 q ha hb
    | true =>
      simp only [d51830, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51831 q = 1) (hb : d61772 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d51831, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51831, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51832 q = 1) (hb : d61773 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d51832, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51832, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51833 q = 1) (hb : d61774 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d51833, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51833, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51834 q = 1) (hb : d61775 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d51834, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51834, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51835 q = 1) (hb : d61776 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d51835, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51835, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5558 (p : Pattern) (ha : d51841 p = 1) (hb : d61782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51836 q = 1) (hb : d61777 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d51836, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5557 q ha hb
    | true =>
      simp only [d51836, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51837 q = 1) (hb : d61778 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d51837, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51837, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51838 q = 1) (hb : d61779 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d51838, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51838, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51839 q = 1) (hb : d61780 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d51839, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51839, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51840 q = 1) (hb : d61781 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d51840, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51840, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51841 q = 1) (hb : d61782 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d51841, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51841, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5559 (p : Pattern) (ha : d51847 p = 1) (hb : d61788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51842 q = 1) (hb : d61783 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d51842, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5558 q ha hb
    | true =>
      simp only [d51842, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51843 q = 1) (hb : d61784 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d51843, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51843, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51844 q = 1) (hb : d61785 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d51844, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51844, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51845 q = 1) (hb : d61786 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d51845, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51845, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51846 q = 1) (hb : d61787 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d51846, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51846, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51847 q = 1) (hb : d61788 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d51847, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51847, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5560 (p : Pattern) (ha : d51853 p = 1) (hb : d61794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51848 q = 1) (hb : d61789 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d51848, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5559 q ha hb
    | true =>
      simp only [d51848, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51849 q = 1) (hb : d61790 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d51849, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51849, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51850 q = 1) (hb : d61791 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d51850, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51850, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51851 q = 1) (hb : d61792 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d51851, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51851, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51852 q = 1) (hb : d61793 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d51852, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51852, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51853 q = 1) (hb : d61794 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d51853, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51853, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5561 (p : Pattern) (ha : d51859 p = 1) (hb : d61800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51854 q = 1) (hb : d61795 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d51854, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5560 q ha hb
    | true =>
      simp only [d51854, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51855 q = 1) (hb : d61796 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d51855, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51855, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51856 q = 1) (hb : d61797 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d51856, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51856, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51857 q = 1) (hb : d61798 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d51857, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51857, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51858 q = 1) (hb : d61799 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d51858, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51858, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51859 q = 1) (hb : d61800 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d51859, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51859, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5562 (p : Pattern) (ha : d51865 p = 1) (hb : d61806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51860 q = 1) (hb : d61801 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d51860, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5561 q ha hb
    | true =>
      simp only [d51860, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51861 q = 1) (hb : d61802 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d51861, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51861, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51862 q = 1) (hb : d61803 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d51862, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51862, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51863 q = 1) (hb : d61804 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d51863, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51863, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51864 q = 1) (hb : d61805 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d51864, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51864, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51865 q = 1) (hb : d61806 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d51865, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51865, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5563 (p : Pattern) (ha : d48 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d47 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d48 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5564 (p : Pattern) (ha : d3324 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3319 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3319, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5563 q ha hb
    | true =>
      simp only [d3319, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3320 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3321 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3322 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3323 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d3324 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5565 (p : Pattern) (ha : d104 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d103 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d104 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5566 (p : Pattern) (ha : d213 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2219 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d213 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5567 (p : Pattern) (ha : d51643 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51643 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5568 (p : Pattern) (ha : d61544 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5565 q ha hb
    | true =>
      simp only [d3329, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3330 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3331 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61539 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61539, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5567 q ha hb
    | true =>
      simp only [d61539, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d214 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5566 q ha hb
    | true =>
      simp only [d214, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61540 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61541 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61542 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61543 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61544 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5569 (p : Pattern) (ha : d284 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d283 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d284 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5570 (p : Pattern) (ha : d397 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2228 q ha hb
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2219 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d103 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d397 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d397, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro5571 (p : Pattern) (ha : d51660 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51660 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51660, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51660, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5572 (p : Pattern) (ha : d61555 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5569 q ha hb
    | true =>
      simp only [d3343, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3344 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3345 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61550 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61550, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5571 q ha hb
    | true =>
      simp only [d61550, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d3347 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3347, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5570 q ha hb
    | true =>
      simp only [d3347, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61551 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61552 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61553 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61554 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61555 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5573 (p : Pattern) (ha : d61561 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3325 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5564 q ha hb
  have h2 (q : Pattern) (ha : d3326 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3327 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3328 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61545 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5568 q ha hb
  have h6 (q : Pattern) (ha : d61546 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61547 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61548 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61549 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61556 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5572 q ha hb
  have h11 (q : Pattern) (ha : d61557 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61558 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61559 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61560 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61561 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5574 (p : Pattern) (ha : d497 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d497 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5575 (p : Pattern) (ha : d638 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d492 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2242 q ha hb
    | true =>
      simp only [d492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2243 q ha hb
  have h2 (q : Pattern) (ha : d493 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d637 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d638 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d638, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d638, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro5576 (p : Pattern) (ha : d51685 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51685 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51685, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51685, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5577 (p : Pattern) (ha : d61567 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5574 q ha hb
    | true =>
      simp only [d3359, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3360 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3361 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61562 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61562, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5576 q ha hb
    | true =>
      simp only [d61562, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d3363 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3363, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5575 q ha hb
    | true =>
      simp only [d3363, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61563 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61564 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61565 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61566 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61567 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5578 (p : Pattern) (ha : d61573 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61568 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5577 q ha hb
  have h2 (q : Pattern) (ha : d61569 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61570 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61571 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61572 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61573 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5579 (p : Pattern) (ha : d789 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d788 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d789 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5580 (p : Pattern) (ha : d944 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d784 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2257 q ha hb
    | true =>
      simp only [d784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2258 q ha hb
  have h2 (q : Pattern) (ha : d785 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d943 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d944 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d944, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d944, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro5581 (p : Pattern) (ha : d51711 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51710 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51711 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51711, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51711, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5582 (p : Pattern) (ha : d61580 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5579 q ha hb
    | true =>
      simp only [d3376, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3377 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3378 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61575 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61575, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5581 q ha hb
    | true =>
      simp only [d61575, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d3380 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3380, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5580 q ha hb
    | true =>
      simp only [d3380, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61576 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61577 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61578 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61579 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61580 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5583 (p : Pattern) (ha : d61586 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61581 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5582 q ha hb
  have h2 (q : Pattern) (ha : d61582 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61583 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61584 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61585 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61586 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5584 (p : Pattern) (ha : d1168 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1167 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1168 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5585 (p : Pattern) (ha : d1355 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2272 q ha hb
    | true =>
      simp only [d1163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2273 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1354 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1355 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1355, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1355, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro5586 (p : Pattern) (ha : d51738 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51737 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51738 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51738, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51738, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5587 (p : Pattern) (ha : d61594 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5584 q ha hb
    | true =>
      simp only [d3394, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3395 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3396 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61589 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61589, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5586 q ha hb
    | true =>
      simp only [d61589, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d3398 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3398, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5585 q ha hb
    | true =>
      simp only [d3398, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61590 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61591 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61592 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61593 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61594 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5588 (p : Pattern) (ha : d61600 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61595 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5587 q ha hb
  have h2 (q : Pattern) (ha : d61596 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61597 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61598 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61599 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61600 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5589 (p : Pattern) (ha : d1629 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1628 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1629 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5590 (p : Pattern) (ha : d1832 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2287 q ha hb
    | true =>
      simp only [d1624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2288 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1831 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1832 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1832, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1832, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro5591 (p : Pattern) (ha : d51766 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51765 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51766 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51766, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51766, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5592 (p : Pattern) (ha : d61609 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5589 q ha hb
    | true =>
      simp only [d3413, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3414 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3415 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61604 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61604, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5591 q ha hb
    | true =>
      simp only [d61604, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d3417 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3417, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5590 q ha hb
    | true =>
      simp only [d3417, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61605 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61606 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61607 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61608 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61609 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5593 (p : Pattern) (ha : d61615 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61610 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5592 q ha hb
  have h2 (q : Pattern) (ha : d61611 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61612 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61613 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61614 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61615 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5594 (p : Pattern) (ha : d2112 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2111 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2112 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5595 (p : Pattern) (ha : d2310 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2302 q ha hb
    | true =>
      simp only [d2107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2303 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2309 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2310 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2310, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2310, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro5596 (p : Pattern) (ha : d51795 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51794 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51795 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51795, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51795, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5597 (p : Pattern) (ha : d61625 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5594 q ha hb
    | true =>
      simp only [d3433, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3434 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3435 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61620 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61620, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5596 q ha hb
    | true =>
      simp only [d61620, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d3437 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3437, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5595 q ha hb
    | true =>
      simp only [d3437, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61621 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61622 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61623 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61624 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61625 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5598 (p : Pattern) (ha : d61631 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61626 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5597 q ha hb
  have h2 (q : Pattern) (ha : d61627 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61628 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61629 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61630 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61631 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5599 (p : Pattern) (ha : d61637 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d61574 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5573 q ha hb
    | true =>
      simp only [d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5578 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61587 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5583 q ha hb
  have h3 (q : Pattern) (ha : d61588 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61601 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5588 q ha hb
  have h5 (q : Pattern) (ha : d61602 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61603 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61616 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5593 q ha hb
  have h8 (q : Pattern) (ha : d61617 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61618 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61619 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61632 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5598 q ha hb
  have h12 (q : Pattern) (ha : d61633 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61634 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61635 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61636 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61637 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5600 (p : Pattern) (ha : d61643 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61638 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5599 q ha hb
    | true =>
      simp only [d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61639 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61640 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61641 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61642 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61643 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5601 (p : Pattern) (ha : d61649 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61644 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5600 q ha hb
    | true =>
      simp only [d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61645 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61646 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61647 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61648 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61649 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5602 (p : Pattern) (ha : d61655 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61650 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5601 q ha hb
    | true =>
      simp only [d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61651 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61652 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61653 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61654 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61655 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5603 (p : Pattern) (ha : d61661 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61656 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5602 q ha hb
    | true =>
      simp only [d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61657 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61658 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61659 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61660 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61661 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5604 (p : Pattern) (ha : d61667 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61662 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5603 q ha hb
    | true =>
      simp only [d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61663 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61664 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61665 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61666 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61667 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5605 (p : Pattern) (ha : d61673 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61668 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5604 q ha hb
    | true =>
      simp only [d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61669 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61670 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61671 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61672 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61673 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5606 (p : Pattern) (ha : d61679 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61674 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5605 q ha hb
    | true =>
      simp only [d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61675 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61676 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61677 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61678 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61679 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5607 (p : Pattern) (ha : d61683 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5565 q ha hb
    | true =>
      simp only [d3329, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3330 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61680 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61681 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61682 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61683 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5608 (p : Pattern) (ha : d61692 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5569 q ha hb
    | true =>
      simp only [d3343, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3344 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61689 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61690 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61691 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61692 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5609 (p : Pattern) (ha : d61698 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61684 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5607 q ha hb
  have h2 (q : Pattern) (ha : d61685 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61686 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61687 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61688 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61693 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5608 q ha hb
  have h7 (q : Pattern) (ha : d61694 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61695 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61696 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61697 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61698 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro5610 (p : Pattern) (ha : d61702 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5574 q ha hb
    | true =>
      simp only [d3359, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3360 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61699 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61700 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61701 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61702 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5611 (p : Pattern) (ha : d61708 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61703 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5610 q ha hb
  have h2 (q : Pattern) (ha : d61704 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61705 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61706 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61707 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61708 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5612 (p : Pattern) (ha : d61713 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5579 q ha hb
    | true =>
      simp only [d3376, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3377 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61710 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61711 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61712 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61713 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5613 (p : Pattern) (ha : d61719 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61714 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5612 q ha hb
  have h2 (q : Pattern) (ha : d61715 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61716 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61717 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61718 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61719 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5614 (p : Pattern) (ha : d61725 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5584 q ha hb
    | true =>
      simp only [d3394, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3395 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61722 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61723 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61724 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61725 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5615 (p : Pattern) (ha : d61731 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61726 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5614 q ha hb
  have h2 (q : Pattern) (ha : d61727 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61728 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61729 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61730 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61731 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5616 (p : Pattern) (ha : d61738 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5589 q ha hb
    | true =>
      simp only [d3413, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3414 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61735 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61736 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61737 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61738 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5617 (p : Pattern) (ha : d61744 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61739 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5616 q ha hb
  have h2 (q : Pattern) (ha : d61740 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61741 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61742 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61743 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61744 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5618 (p : Pattern) (ha : d61752 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5594 q ha hb
    | true =>
      simp only [d3433, d73493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3434 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61749 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61750 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61751 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61752 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5619 (p : Pattern) (ha : d61758 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61753 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5618 q ha hb
  have h2 (q : Pattern) (ha : d61754 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61755 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61756 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61757 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61758 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5620 (p : Pattern) (ha : d61764 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d61709 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5609 q ha hb
    | true =>
      simp only [d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5611 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61720 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5613 q ha hb
  have h3 (q : Pattern) (ha : d61721 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61732 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5615 q ha hb
  have h5 (q : Pattern) (ha : d61733 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61734 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61745 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5617 q ha hb
  have h8 (q : Pattern) (ha : d61746 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61747 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61748 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61759 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5619 q ha hb
  have h12 (q : Pattern) (ha : d61760 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61761 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61762 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61763 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61764 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5621 (p : Pattern) (ha : d61770 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61765 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5620 q ha hb
    | true =>
      simp only [d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61766 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61767 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61768 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61769 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61770 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5622 (p : Pattern) (ha : d61776 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61771 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5621 q ha hb
    | true =>
      simp only [d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61772 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61773 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61774 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61775 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61776 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5623 (p : Pattern) (ha : d61782 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61777 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5622 q ha hb
    | true =>
      simp only [d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61778 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61779 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61780 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61781 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61782 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5624 (p : Pattern) (ha : d61788 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61783 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5623 q ha hb
    | true =>
      simp only [d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61784 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61785 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61786 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61787 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61788 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5625 (p : Pattern) (ha : d61794 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61789 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5624 q ha hb
    | true =>
      simp only [d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61790 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61791 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61792 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61793 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61794 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5626 (p : Pattern) (ha : d61800 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61795 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5625 q ha hb
    | true =>
      simp only [d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61796 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61797 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61798 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61799 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61800 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5627 (p : Pattern) (ha : d61806 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61801 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5626 q ha hb
    | true =>
      simp only [d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61802 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61803 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61804 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61805 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61806 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5628 (p : Pattern) (ha : d61544 p = 1) (hb : d73495 p = 1) : d73501 p = 1 := by
  have h0 (q : Pattern) (ha : d3331 q = 1) (hb : d73495 q = 1) : d3331 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61539 q = 1) (hb : d73494 q = 1) : d73496 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61539, d73494, d73496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4201 q ha hb
    | true =>
      simp only [d61539, d73494, d73496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d61540 q = 1) (hb : d73495 q = 1) : d73497 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61540, d73495, d73497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61540, d73495, d73497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d61541 q = 1) (hb : d73495 q = 1) : d73498 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61541, d73498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61541, d73498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61542 q = 1) (hb : d73495 q = 1) : d73499 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61542, d73499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61542, d73499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61543 q = 1) (hb : d73495 q = 1) : d73500 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61543, d73500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61543, d73500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d61544 q = 1) (hb : d73495 q = 1) : d73501 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61544, d73501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61544, d73501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5629 (p : Pattern) (ha : d61555 p = 1) (hb : d73495 p = 1) : d73515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d73494 q = 1) : d73507 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d73494, d73507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4204 q ha hb
    | true =>
      simp only [d3343, d73494, d73507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3344 q = 1) (hb : d73495 q = 1) : d73508 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d73495, d73508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d73495, d73508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d3345 q = 1) (hb : d73495 q = 1) : d73509 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3345, d73509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3345, d73509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61550 q = 1) (hb : d73494 q = 1) : d73510 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61550, d73494, d73510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4208 q ha hb
    | true =>
      simp only [d61550, d73494, d73510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d3347 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d61551 q = 1) (hb : d73495 q = 1) : d73511 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61551, d73495, d73511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61551, d73495, d73511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d61552 q = 1) (hb : d73495 q = 1) : d73512 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61552, d73512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61552, d73512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61553 q = 1) (hb : d73495 q = 1) : d73513 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61553, d73513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61553, d73513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61554 q = 1) (hb : d73495 q = 1) : d73514 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61554, d73514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61554, d73514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61555 q = 1) (hb : d73495 q = 1) : d73515 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61555, d73515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61555, d73515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5630 (p : Pattern) (ha : d61561 p = 1) (hb : d73495 p = 1) : d73521 p = 1 := by
  have h0 (q : Pattern) (ha : d3328 q = 1) (hb : d73495 q = 1) : d3328 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61545 q = 1) (hb : d73495 q = 1) : d73502 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61545, d73502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61545, d73502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5628 q ha hb
  have h3 (q : Pattern) (ha : d61546 q = 1) (hb : d73495 q = 1) : d73503 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61546, d73503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61546, d73503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61547 q = 1) (hb : d73495 q = 1) : d73504 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61547, d73504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61547, d73504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61548 q = 1) (hb : d73495 q = 1) : d73505 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61548, d73505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61548, d73505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61549 q = 1) (hb : d73495 q = 1) : d73506 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61549, d73506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61549, d73506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61556 q = 1) (hb : d73495 q = 1) : d73516 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61556, d73516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61556, d73516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5629 q ha hb
  have h8 (q : Pattern) (ha : d61557 q = 1) (hb : d73495 q = 1) : d73517 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61557, d73517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61557, d73517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61558 q = 1) (hb : d73495 q = 1) : d73518 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61558, d73518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61558, d73518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61559 q = 1) (hb : d73495 q = 1) : d73519 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61559, d73519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61559, d73519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61560 q = 1) (hb : d73495 q = 1) : d73520 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61560, d73520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61560, d73520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61561 q = 1) (hb : d73495 q = 1) : d73521 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61561, d73521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61561, d73521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5631 (p : Pattern) (ha : d61567 p = 1) (hb : d73495 p = 1) : d73530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d73494 q = 1) : d73522 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d73494, d73522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4212 q ha hb
    | true =>
      simp only [d3359, d73494, d73522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3360 q = 1) (hb : d73495 q = 1) : d73523 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d73495, d73523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d73495, d73523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d3361 q = 1) (hb : d73495 q = 1) : d73524 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3361, d73524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3361, d73524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61562 q = 1) (hb : d73494 q = 1) : d73525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61562, d73494, d73525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4216 q ha hb
    | true =>
      simp only [d61562, d73494, d73525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d3363 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d61563 q = 1) (hb : d73495 q = 1) : d73526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61563, d73495, d73526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61563, d73495, d73526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d61564 q = 1) (hb : d73495 q = 1) : d73527 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61564, d73527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61564, d73527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61565 q = 1) (hb : d73495 q = 1) : d73528 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61565, d73528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61565, d73528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61566 q = 1) (hb : d73495 q = 1) : d73529 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61566, d73529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61566, d73529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61567 q = 1) (hb : d73495 q = 1) : d73530 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61567, d73530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61567, d73530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5632 (p : Pattern) (ha : d61573 p = 1) (hb : d73495 p = 1) : d73536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61568 q = 1) (hb : d73495 q = 1) : d73531 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61568, d73531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61568, d73531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5631 q ha hb
  have h2 (q : Pattern) (ha : d61569 q = 1) (hb : d73495 q = 1) : d73532 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61569, d73532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61569, d73532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61570 q = 1) (hb : d73495 q = 1) : d73533 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61570, d73533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61570, d73533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61571 q = 1) (hb : d73495 q = 1) : d73534 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61571, d73534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61571, d73534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61572 q = 1) (hb : d73495 q = 1) : d73535 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61572, d73535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61572, d73535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61573 q = 1) (hb : d73495 q = 1) : d73536 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61573, d73536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61573, d73536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5633 (p : Pattern) (ha : d61580 p = 1) (hb : d73495 p = 1) : d73546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d73494 q = 1) : d73538 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d73494, d73538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4220 q ha hb
    | true =>
      simp only [d3376, d73494, d73538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3377 q = 1) (hb : d73495 q = 1) : d73539 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d73495, d73539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d73495, d73539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d3378 q = 1) (hb : d73495 q = 1) : d73540 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3378, d73540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3378, d73540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61575 q = 1) (hb : d73494 q = 1) : d73541 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61575, d73494, d73541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4224 q ha hb
    | true =>
      simp only [d61575, d73494, d73541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d3380 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d61576 q = 1) (hb : d73495 q = 1) : d73542 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61576, d73495, d73542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61576, d73495, d73542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d61577 q = 1) (hb : d73495 q = 1) : d73543 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61577, d73543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61577, d73543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61578 q = 1) (hb : d73495 q = 1) : d73544 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61578, d73544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61578, d73544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61579 q = 1) (hb : d73495 q = 1) : d73545 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61579, d73545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61579, d73545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61580 q = 1) (hb : d73495 q = 1) : d73546 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61580, d73546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61580, d73546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5634 (p : Pattern) (ha : d61586 p = 1) (hb : d73495 p = 1) : d73552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61581 q = 1) (hb : d73495 q = 1) : d73547 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61581, d73547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61581, d73547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5633 q ha hb
  have h2 (q : Pattern) (ha : d61582 q = 1) (hb : d73495 q = 1) : d73548 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61582, d73548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61582, d73548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61583 q = 1) (hb : d73495 q = 1) : d73549 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61583, d73549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61583, d73549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61584 q = 1) (hb : d73495 q = 1) : d73550 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61584, d73550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61584, d73550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61585 q = 1) (hb : d73495 q = 1) : d73551 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61585, d73551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61585, d73551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61586 q = 1) (hb : d73495 q = 1) : d73552 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61586, d73552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61586, d73552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5635 (p : Pattern) (ha : d61594 p = 1) (hb : d73495 p = 1) : d73563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d73494 q = 1) : d73555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d73494, d73555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4228 q ha hb
    | true =>
      simp only [d3394, d73494, d73555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3395 q = 1) (hb : d73495 q = 1) : d73556 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d73495, d73556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d73495, d73556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d3396 q = 1) (hb : d73495 q = 1) : d73557 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3396, d73557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3396, d73557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61589 q = 1) (hb : d73494 q = 1) : d73558 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61589, d73494, d73558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4232 q ha hb
    | true =>
      simp only [d61589, d73494, d73558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d3398 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d61590 q = 1) (hb : d73495 q = 1) : d73559 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61590, d73495, d73559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61590, d73495, d73559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d61591 q = 1) (hb : d73495 q = 1) : d73560 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61591, d73560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61591, d73560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61592 q = 1) (hb : d73495 q = 1) : d73561 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61592, d73561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61592, d73561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61593 q = 1) (hb : d73495 q = 1) : d73562 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61593, d73562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61593, d73562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61594 q = 1) (hb : d73495 q = 1) : d73563 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61594, d73563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61594, d73563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5636 (p : Pattern) (ha : d61600 p = 1) (hb : d73495 p = 1) : d73569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61595 q = 1) (hb : d73495 q = 1) : d73564 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61595, d73564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61595, d73564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5635 q ha hb
  have h2 (q : Pattern) (ha : d61596 q = 1) (hb : d73495 q = 1) : d73565 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61596, d73565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61596, d73565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61597 q = 1) (hb : d73495 q = 1) : d73566 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61597, d73566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61597, d73566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61598 q = 1) (hb : d73495 q = 1) : d73567 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61598, d73567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61598, d73567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61599 q = 1) (hb : d73495 q = 1) : d73568 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61599, d73568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61599, d73568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61600 q = 1) (hb : d73495 q = 1) : d73569 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61600, d73569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61600, d73569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5637 (p : Pattern) (ha : d61609 p = 1) (hb : d73495 p = 1) : d73581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d73494 q = 1) : d73573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d73494, d73573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4236 q ha hb
    | true =>
      simp only [d3413, d73494, d73573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3414 q = 1) (hb : d73495 q = 1) : d73574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d73495, d73574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d73495, d73574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d3415 q = 1) (hb : d73495 q = 1) : d73575 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3415, d73575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3415, d73575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61604 q = 1) (hb : d73494 q = 1) : d73576 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61604, d73494, d73576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4240 q ha hb
    | true =>
      simp only [d61604, d73494, d73576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d3417 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d61605 q = 1) (hb : d73495 q = 1) : d73577 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61605, d73495, d73577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61605, d73495, d73577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d61606 q = 1) (hb : d73495 q = 1) : d73578 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61606, d73578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61606, d73578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61607 q = 1) (hb : d73495 q = 1) : d73579 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61607, d73579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61607, d73579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61608 q = 1) (hb : d73495 q = 1) : d73580 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61608, d73580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61608, d73580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61609 q = 1) (hb : d73495 q = 1) : d73581 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61609, d73581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61609, d73581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5638 (p : Pattern) (ha : d61615 p = 1) (hb : d73495 p = 1) : d73587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61610 q = 1) (hb : d73495 q = 1) : d73582 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61610, d73582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61610, d73582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5637 q ha hb
  have h2 (q : Pattern) (ha : d61611 q = 1) (hb : d73495 q = 1) : d73583 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61611, d73583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61611, d73583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61612 q = 1) (hb : d73495 q = 1) : d73584 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61612, d73584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61612, d73584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61613 q = 1) (hb : d73495 q = 1) : d73585 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61613, d73585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61613, d73585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61614 q = 1) (hb : d73495 q = 1) : d73586 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61614, d73586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61614, d73586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61615 q = 1) (hb : d73495 q = 1) : d73587 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61615, d73587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61615, d73587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5639 (p : Pattern) (ha : d61625 p = 1) (hb : d73495 p = 1) : d73600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d73494 q = 1) : d73592 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d73494, d73592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4244 q ha hb
    | true =>
      simp only [d3433, d73494, d73592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3434 q = 1) (hb : d73495 q = 1) : d73593 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d73495, d73593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d73495, d73593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d3435 q = 1) (hb : d73495 q = 1) : d73594 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3435, d73594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3435, d73594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61620 q = 1) (hb : d73494 q = 1) : d73595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61620, d73494, d73595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4248 q ha hb
    | true =>
      simp only [d61620, d73494, d73595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d3437 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d61621 q = 1) (hb : d73495 q = 1) : d73596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61621, d73495, d73596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61621, d73495, d73596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d61622 q = 1) (hb : d73495 q = 1) : d73597 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61622, d73597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61622, d73597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61623 q = 1) (hb : d73495 q = 1) : d73598 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61623, d73598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61623, d73598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61624 q = 1) (hb : d73495 q = 1) : d73599 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61624, d73599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61624, d73599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61625 q = 1) (hb : d73495 q = 1) : d73600 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61625, d73600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61625, d73600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5640 (p : Pattern) (ha : d61631 p = 1) (hb : d73495 p = 1) : d73606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61626 q = 1) (hb : d73495 q = 1) : d73601 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61626, d73601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61626, d73601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5639 q ha hb
  have h2 (q : Pattern) (ha : d61627 q = 1) (hb : d73495 q = 1) : d73602 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61627, d73602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61627, d73602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61628 q = 1) (hb : d73495 q = 1) : d73603 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61628, d73603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61628, d73603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61629 q = 1) (hb : d73495 q = 1) : d73604 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61629, d73604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61629, d73604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61630 q = 1) (hb : d73495 q = 1) : d73605 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61630, d73605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61630, d73605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61631 q = 1) (hb : d73495 q = 1) : d73606 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61631, d73606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61631, d73606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5641 (p : Pattern) (ha : d61637 p = 1) (hb : d73495 p = 1) : d73612 p = 1 := by
  have h0 (q : Pattern) (ha : d61574 q = 1) (hb : d73495 q = 1) : d73537 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61574, d73537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5630 q ha hb
    | true =>
      simp only [d61574, d73537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5632 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61587 q = 1) (hb : d73495 q = 1) : d73553 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61587, d73553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61587, d73553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5634 q ha hb
  have h3 (q : Pattern) (ha : d61588 q = 1) (hb : d73495 q = 1) : d73554 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61588, d73554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61588, d73554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61601 q = 1) (hb : d73495 q = 1) : d73570 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61601, d73570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61601, d73570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5636 q ha hb
  have h5 (q : Pattern) (ha : d61602 q = 1) (hb : d73495 q = 1) : d73571 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61602, d73571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61602, d73571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61603 q = 1) (hb : d73495 q = 1) : d73572 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61603, d73572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61603, d73572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61616 q = 1) (hb : d73495 q = 1) : d73588 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61616, d73588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61616, d73588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5638 q ha hb
  have h8 (q : Pattern) (ha : d61617 q = 1) (hb : d73495 q = 1) : d73589 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61617, d73589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61617, d73589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61618 q = 1) (hb : d73495 q = 1) : d73590 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61618, d73590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61618, d73590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61619 q = 1) (hb : d73495 q = 1) : d73591 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61619, d73591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61619, d73591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61632 q = 1) (hb : d73495 q = 1) : d73607 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61632, d73607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61632, d73607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5640 q ha hb
  have h12 (q : Pattern) (ha : d61633 q = 1) (hb : d73495 q = 1) : d73608 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61633, d73608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61633, d73608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61634 q = 1) (hb : d73495 q = 1) : d73609 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61634, d73609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61634, d73609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61635 q = 1) (hb : d73495 q = 1) : d73610 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61635, d73610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61635, d73610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61636 q = 1) (hb : d73495 q = 1) : d73611 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61636, d73611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61636, d73611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61637 q = 1) (hb : d73495 q = 1) : d73612 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61637, d73612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61637, d73612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5642 (p : Pattern) (ha : d61643 p = 1) (hb : d73495 p = 1) : d73618 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61638 q = 1) (hb : d73495 q = 1) : d73613 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61638, d73613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5641 q ha hb
    | true =>
      simp only [d61638, d73613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61639 q = 1) (hb : d73495 q = 1) : d73614 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61639, d73614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61639, d73614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61640 q = 1) (hb : d73495 q = 1) : d73615 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61640, d73615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61640, d73615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61641 q = 1) (hb : d73495 q = 1) : d73616 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61641, d73616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61641, d73616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61642 q = 1) (hb : d73495 q = 1) : d73617 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61642, d73617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61642, d73617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61643 q = 1) (hb : d73495 q = 1) : d73618 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61643, d73618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61643, d73618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5643 (p : Pattern) (ha : d61649 p = 1) (hb : d73495 p = 1) : d73624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61644 q = 1) (hb : d73495 q = 1) : d73619 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61644, d73619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5642 q ha hb
    | true =>
      simp only [d61644, d73619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61645 q = 1) (hb : d73495 q = 1) : d73620 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61645, d73620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61645, d73620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61646 q = 1) (hb : d73495 q = 1) : d73621 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61646, d73621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61646, d73621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61647 q = 1) (hb : d73495 q = 1) : d73622 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61647, d73622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61647, d73622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61648 q = 1) (hb : d73495 q = 1) : d73623 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61648, d73623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61648, d73623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61649 q = 1) (hb : d73495 q = 1) : d73624 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61649, d73624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61649, d73624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5644 (p : Pattern) (ha : d61655 p = 1) (hb : d73495 p = 1) : d73630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61650 q = 1) (hb : d73495 q = 1) : d73625 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61650, d73625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5643 q ha hb
    | true =>
      simp only [d61650, d73625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61651 q = 1) (hb : d73495 q = 1) : d73626 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61651, d73626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61651, d73626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61652 q = 1) (hb : d73495 q = 1) : d73627 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61652, d73627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61652, d73627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61653 q = 1) (hb : d73495 q = 1) : d73628 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61653, d73628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61653, d73628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61654 q = 1) (hb : d73495 q = 1) : d73629 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61654, d73629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61654, d73629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61655 q = 1) (hb : d73495 q = 1) : d73630 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61655, d73630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61655, d73630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5645 (p : Pattern) (ha : d61661 p = 1) (hb : d73495 p = 1) : d73636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61656 q = 1) (hb : d73495 q = 1) : d73631 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61656, d73631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5644 q ha hb
    | true =>
      simp only [d61656, d73631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61657 q = 1) (hb : d73495 q = 1) : d73632 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61657, d73632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61657, d73632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61658 q = 1) (hb : d73495 q = 1) : d73633 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61658, d73633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61658, d73633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61659 q = 1) (hb : d73495 q = 1) : d73634 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61659, d73634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61659, d73634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61660 q = 1) (hb : d73495 q = 1) : d73635 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61660, d73635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61660, d73635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61661 q = 1) (hb : d73495 q = 1) : d73636 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61661, d73636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61661, d73636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5646 (p : Pattern) (ha : d61667 p = 1) (hb : d73495 p = 1) : d73642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61662 q = 1) (hb : d73495 q = 1) : d73637 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61662, d73637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5645 q ha hb
    | true =>
      simp only [d61662, d73637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61663 q = 1) (hb : d73495 q = 1) : d73638 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61663, d73638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61663, d73638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61664 q = 1) (hb : d73495 q = 1) : d73639 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61664, d73639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61664, d73639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61665 q = 1) (hb : d73495 q = 1) : d73640 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61665, d73640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61665, d73640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61666 q = 1) (hb : d73495 q = 1) : d73641 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61666, d73641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61666, d73641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61667 q = 1) (hb : d73495 q = 1) : d73642 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61667, d73642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61667, d73642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5647 (p : Pattern) (ha : d61673 p = 1) (hb : d73495 p = 1) : d73648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61668 q = 1) (hb : d73495 q = 1) : d73643 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61668, d73643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5646 q ha hb
    | true =>
      simp only [d61668, d73643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61669 q = 1) (hb : d73495 q = 1) : d73644 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61669, d73644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61669, d73644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61670 q = 1) (hb : d73495 q = 1) : d73645 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61670, d73645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61670, d73645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61671 q = 1) (hb : d73495 q = 1) : d73646 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61671, d73646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61671, d73646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61672 q = 1) (hb : d73495 q = 1) : d73647 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61672, d73647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61672, d73647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61673 q = 1) (hb : d73495 q = 1) : d73648 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61673, d73648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61673, d73648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5648 (p : Pattern) (ha : d61679 p = 1) (hb : d73495 p = 1) : d73654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61674 q = 1) (hb : d73495 q = 1) : d73649 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61674, d73649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5647 q ha hb
    | true =>
      simp only [d61674, d73649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61675 q = 1) (hb : d73495 q = 1) : d73650 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61675, d73650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61675, d73650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61676 q = 1) (hb : d73495 q = 1) : d73651 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61676, d73651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61676, d73651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61677 q = 1) (hb : d73495 q = 1) : d73652 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61677, d73652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61677, d73652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61678 q = 1) (hb : d73495 q = 1) : d73653 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61678, d73653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61678, d73653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61679 q = 1) (hb : d73495 q = 1) : d73654 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61679, d73654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61679, d73654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5649 (p : Pattern) (ha : d68784 p = 1) (hb : d73501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51963 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d3329, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3331 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3331, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3331, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d68761 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d68762 q = 1) (hb : d73496 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68762, d73496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4260 q ha hb
    | true =>
      simp only [d68762, d73496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d68763 q = 1) (hb : d73497 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68763, d73497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68763, d73497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d68764 q = 1) (hb : d73498 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68764, d73498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68764, d73498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d68765 q = 1) (hb : d73499 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68765, d73499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d68765, d73499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d68772 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d68773 q = 1) (hb : d73500 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68773, d73500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68773, d73500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d68783 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d68784 q = 1) (hb : d73501 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68784, d73501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68784, d73501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro5650 (p : Pattern) (ha : d68865 p = 1) (hb : d73515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68796 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d68802 q = 1) (hb : d73507 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68802, d73507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4265 q hb ha
    | true =>
      simp only [d68802, d73507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d68803 q = 1) (hb : d73508 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68803, d73508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68803, d73508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d68804 q = 1) (hb : d73509 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68804, d73509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68804, d73509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d68830 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d68831 q = 1) (hb : d73510 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68831, d73510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4267 q ha hb
    | true =>
      simp only [d68831, d73510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d68842 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d68843 q = 1) (hb : d73511 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68843, d73511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68843, d73511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d68844 q = 1) (hb : d73512 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68844, d73512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68844, d73512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d68845 q = 1) (hb : d73513 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68845, d73513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68845, d73513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d68852 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d68853 q = 1) (hb : d73514 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68853, d73514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68853, d73514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d68864 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d68865 q = 1) (hb : d73515 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68865, d73515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68865, d73515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro5651 (p : Pattern) (ha : d68871 p = 1) (hb : d73521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3325 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3325, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3325, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5367 q ha hb
  have h2 (q : Pattern) (ha : d3326 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3326, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3326, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3327 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3327, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3327, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3328 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3328, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3328, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68785 q = 1) (hb : d73502 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68785, d73502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68785, d73502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5649 q ha hb
  have h6 (q : Pattern) (ha : d68786 q = 1) (hb : d73503 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68786, d73503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68786, d73503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68787 q = 1) (hb : d73504 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68787, d73504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68787, d73504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68788 q = 1) (hb : d73505 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68788, d73505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68788, d73505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68789 q = 1) (hb : d73506 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68789, d73506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d68789, d73506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68866 q = 1) (hb : d73516 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68866, d73516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68866, d73516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5650 q ha hb
  have h11 (q : Pattern) (ha : d68867 q = 1) (hb : d73517 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68867, d73517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68867, d73517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d68868 q = 1) (hb : d73518 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68868, d73518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68868, d73518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68869 q = 1) (hb : d73519 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68869, d73519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68869, d73519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d68870 q = 1) (hb : d73520 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68870, d73520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68870, d73520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d68871 q = 1) (hb : d73521 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68871, d73521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68871, d73521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5652 (p : Pattern) (ha : d68956 p = 1) (hb : d73530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d68884 q = 1) (hb : d73522 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68884, d73522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4273 q hb ha
    | true =>
      simp only [d68884, d73522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d68885 q = 1) (hb : d73523 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68885, d73523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68885, d73523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d68886 q = 1) (hb : d73524 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68886, d73524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68886, d73524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d68912 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d68913 q = 1) (hb : d73525 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68913, d73525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4275 q ha hb
    | true =>
      simp only [d68913, d73525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d68933 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d68934 q = 1) (hb : d73526 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68934, d73526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68934, d73526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d68935 q = 1) (hb : d73527 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68935, d73527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68935, d73527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d68936 q = 1) (hb : d73528 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68936, d73528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68936, d73528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d68943 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d68944 q = 1) (hb : d73529 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68944, d73529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68944, d73529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d68955 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d68956 q = 1) (hb : d73530 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68956, d73530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68956, d73530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro5653 (p : Pattern) (ha : d68962 p = 1) (hb : d73536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68957 q = 1) (hb : d73531 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68957, d73531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68957, d73531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5652 q ha hb
  have h2 (q : Pattern) (ha : d68958 q = 1) (hb : d73532 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68958, d73532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68958, d73532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68959 q = 1) (hb : d73533 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68959, d73533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68959, d73533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68960 q = 1) (hb : d73534 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68960, d73534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68960, d73534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68961 q = 1) (hb : d73535 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68961, d73535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68961, d73535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68962 q = 1) (hb : d73536 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68962, d73536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68962, d73536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5654 (p : Pattern) (ha : d69048 p = 1) (hb : d73546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68970 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68975 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d68976 q = 1) (hb : d73538 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68976, d73538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4281 q hb ha
    | true =>
      simp only [d68976, d73538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d68977 q = 1) (hb : d73539 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68977, d73539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68977, d73539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d68978 q = 1) (hb : d73540 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68978, d73540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68978, d73540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d69004 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d69005 q = 1) (hb : d73541 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69005, d73541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4283 q ha hb
    | true =>
      simp only [d69005, d73541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d69025 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69026 q = 1) (hb : d73542 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69026, d73542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69026, d73542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d69027 q = 1) (hb : d73543 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69027, d73543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69027, d73543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d69028 q = 1) (hb : d73544 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69028, d73544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69028, d73544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d69035 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d69036 q = 1) (hb : d73545 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69036, d73545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69036, d73545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d69047 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69048 q = 1) (hb : d73546 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69048, d73546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69048, d73546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro5655 (p : Pattern) (ha : d69054 p = 1) (hb : d73552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69049 q = 1) (hb : d73547 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69049, d73547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69049, d73547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5654 q ha hb
  have h2 (q : Pattern) (ha : d69050 q = 1) (hb : d73548 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69050, d73548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69050, d73548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69051 q = 1) (hb : d73549 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69051, d73549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69051, d73549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69052 q = 1) (hb : d73550 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69052, d73550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69052, d73550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69053 q = 1) (hb : d73551 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69053, d73551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69053, d73551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69054 q = 1) (hb : d73552 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69054, d73552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69054, d73552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5656 (p : Pattern) (ha : d69155 p = 1) (hb : d73563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69063 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69068 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69069 q = 1) (hb : d73555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69069, d73555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4289 q hb ha
    | true =>
      simp only [d69069, d73555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69070 q = 1) (hb : d73556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69070, d73556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69070, d73556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d69071 q = 1) (hb : d73557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69071, d73557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69071, d73557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d69097 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d69098 q = 1) (hb : d73558 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69098, d73558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4291 q ha hb
    | true =>
      simp only [d69098, d73558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d69132 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69133 q = 1) (hb : d73559 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69133, d73559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69133, d73559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d69134 q = 1) (hb : d73560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69134, d73560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69134, d73560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d69135 q = 1) (hb : d73561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69135, d73561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69135, d73561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d69142 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d69143 q = 1) (hb : d73562 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69143, d73562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69143, d73562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d69154 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69155 q = 1) (hb : d73563 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69155, d73563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69155, d73563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro5657 (p : Pattern) (ha : d69161 p = 1) (hb : d73569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69156 q = 1) (hb : d73564 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69156, d73564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69156, d73564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5656 q ha hb
  have h2 (q : Pattern) (ha : d69157 q = 1) (hb : d73565 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69157, d73565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69157, d73565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69158 q = 1) (hb : d73566 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69158, d73566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69158, d73566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69159 q = 1) (hb : d73567 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69159, d73567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69159, d73567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69160 q = 1) (hb : d73568 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69160, d73568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69160, d73568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69161 q = 1) (hb : d73569 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69161, d73569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69161, d73569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5658 (p : Pattern) (ha : d69268 p = 1) (hb : d73581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69171 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69176 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69177 q = 1) (hb : d73573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69177, d73573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4297 q hb ha
    | true =>
      simp only [d69177, d73573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69178 q = 1) (hb : d73574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69178, d73574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69178, d73574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d69179 q = 1) (hb : d73575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69179, d73575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69179, d73575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d69205 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d69206 q = 1) (hb : d73576 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69206, d73576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4299 q ha hb
    | true =>
      simp only [d69206, d73576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d69245 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69246 q = 1) (hb : d73577 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69246, d73577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69246, d73577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d69247 q = 1) (hb : d73578 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69247, d73578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69247, d73578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d69248 q = 1) (hb : d73579 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69248, d73579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69248, d73579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d69255 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d69256 q = 1) (hb : d73580 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69256, d73580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69256, d73580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d69267 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69268 q = 1) (hb : d73581 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69268, d73581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69268, d73581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro5659 (p : Pattern) (ha : d69274 p = 1) (hb : d73587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69269 q = 1) (hb : d73582 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69269, d73582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69269, d73582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5658 q ha hb
  have h2 (q : Pattern) (ha : d69270 q = 1) (hb : d73583 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69270, d73583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69270, d73583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69271 q = 1) (hb : d73584 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69271, d73584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69271, d73584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69272 q = 1) (hb : d73585 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69272, d73585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69272, d73585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69273 q = 1) (hb : d73586 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69273, d73586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69273, d73586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69274 q = 1) (hb : d73587 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69274, d73587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69274, d73587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5660 (p : Pattern) (ha : d69378 p = 1) (hb : d73600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69285 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69290 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69291 q = 1) (hb : d73592 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69291, d73592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4305 q hb ha
    | true =>
      simp only [d69291, d73592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69292 q = 1) (hb : d73593 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69292, d73593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69292, d73593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d69293 q = 1) (hb : d73594 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69293, d73594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69293, d73594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d69319 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d69320 q = 1) (hb : d73595 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69320, d73595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4307 q ha hb
    | true =>
      simp only [d69320, d73595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d69355 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69356 q = 1) (hb : d73596 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69356, d73596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69356, d73596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d69357 q = 1) (hb : d73597 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69357, d73597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69357, d73597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d69358 q = 1) (hb : d73598 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69358, d73598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69358, d73598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d69365 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d69366 q = 1) (hb : d73599 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69366, d73599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69366, d73599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d69377 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69378 q = 1) (hb : d73600 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69378, d73600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69378, d73600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro5661 (p : Pattern) (ha : d69384 p = 1) (hb : d73606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69379 q = 1) (hb : d73601 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69379, d73601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69379, d73601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5660 q ha hb
  have h2 (q : Pattern) (ha : d69380 q = 1) (hb : d73602 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69380, d73602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69380, d73602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69381 q = 1) (hb : d73603 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69381, d73603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69381, d73603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69382 q = 1) (hb : d73604 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69382, d73604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69382, d73604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69383 q = 1) (hb : d73605 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69383, d73605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69383, d73605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69384 q = 1) (hb : d73606 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69384, d73606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69384, d73606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5662 (p : Pattern) (ha : d69390 p = 1) (hb : d73612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d68963 q = 1) (hb : d73537 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68963, d73537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5651 q ha hb
    | true =>
      simp only [d68963, d73537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5653 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69055 q = 1) (hb : d73553 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69055, d73553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69055, d73553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5655 q ha hb
  have h3 (q : Pattern) (ha : d69056 q = 1) (hb : d73554 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69056, d73554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69056, d73554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69162 q = 1) (hb : d73570 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69162, d73570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69162, d73570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5657 q ha hb
  have h5 (q : Pattern) (ha : d69163 q = 1) (hb : d73571 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69163, d73571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69163, d73571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69164 q = 1) (hb : d73572 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69164, d73572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69164, d73572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69275 q = 1) (hb : d73588 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69275, d73588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69275, d73588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5659 q ha hb
  have h8 (q : Pattern) (ha : d69276 q = 1) (hb : d73589 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69276, d73589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69276, d73589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69277 q = 1) (hb : d73590 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69277, d73590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69277, d73590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69278 q = 1) (hb : d73591 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69278, d73591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69278, d73591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69385 q = 1) (hb : d73607 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69385, d73607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69385, d73607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5661 q ha hb
  have h12 (q : Pattern) (ha : d69386 q = 1) (hb : d73608 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69386, d73608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69386, d73608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69387 q = 1) (hb : d73609 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69387, d73609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69387, d73609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69388 q = 1) (hb : d73610 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69388, d73610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69388, d73610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69389 q = 1) (hb : d73611 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d69389, d73611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69389, d73611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69390 q = 1) (hb : d73612 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d69390, d73612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69390, d73612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5663 (p : Pattern) (ha : d69396 p = 1) (hb : d73618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69391 q = 1) (hb : d73613 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d69391, d73613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5662 q ha hb
    | true =>
      simp only [d69391, d73613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69392 q = 1) (hb : d73614 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d69392, d73614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69392, d73614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69393 q = 1) (hb : d73615 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d69393, d73615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69393, d73615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69394 q = 1) (hb : d73616 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d69394, d73616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69394, d73616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69395 q = 1) (hb : d73617 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d69395, d73617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69395, d73617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69396 q = 1) (hb : d73618 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d69396, d73618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69396, d73618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5664 (p : Pattern) (ha : d69402 p = 1) (hb : d73624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69397 q = 1) (hb : d73619 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d69397, d73619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5663 q ha hb
    | true =>
      simp only [d69397, d73619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69398 q = 1) (hb : d73620 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d69398, d73620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69398, d73620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69399 q = 1) (hb : d73621 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d69399, d73621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69399, d73621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69400 q = 1) (hb : d73622 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d69400, d73622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69400, d73622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69401 q = 1) (hb : d73623 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d69401, d73623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69401, d73623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69402 q = 1) (hb : d73624 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d69402, d73624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69402, d73624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5665 (p : Pattern) (ha : d69408 p = 1) (hb : d73630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69403 q = 1) (hb : d73625 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d69403, d73625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5664 q ha hb
    | true =>
      simp only [d69403, d73625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69404 q = 1) (hb : d73626 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d69404, d73626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69404, d73626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69405 q = 1) (hb : d73627 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d69405, d73627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69405, d73627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69406 q = 1) (hb : d73628 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d69406, d73628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69406, d73628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69407 q = 1) (hb : d73629 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d69407, d73629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69407, d73629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69408 q = 1) (hb : d73630 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d69408, d73630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69408, d73630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5666 (p : Pattern) (ha : d69414 p = 1) (hb : d73636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69409 q = 1) (hb : d73631 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d69409, d73631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5665 q ha hb
    | true =>
      simp only [d69409, d73631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69410 q = 1) (hb : d73632 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d69410, d73632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69410, d73632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69411 q = 1) (hb : d73633 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d69411, d73633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69411, d73633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69412 q = 1) (hb : d73634 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d69412, d73634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69412, d73634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69413 q = 1) (hb : d73635 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d69413, d73635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69413, d73635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69414 q = 1) (hb : d73636 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d69414, d73636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69414, d73636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5667 (p : Pattern) (ha : d69420 p = 1) (hb : d73642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69415 q = 1) (hb : d73637 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d69415, d73637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5666 q ha hb
    | true =>
      simp only [d69415, d73637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69416 q = 1) (hb : d73638 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d69416, d73638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69416, d73638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69417 q = 1) (hb : d73639 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d69417, d73639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69417, d73639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69418 q = 1) (hb : d73640 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d69418, d73640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69418, d73640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69419 q = 1) (hb : d73641 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d69419, d73641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69419, d73641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69420 q = 1) (hb : d73642 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d69420, d73642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69420, d73642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5668 (p : Pattern) (ha : d69426 p = 1) (hb : d73648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69421 q = 1) (hb : d73643 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d69421, d73643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5667 q ha hb
    | true =>
      simp only [d69421, d73643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69422 q = 1) (hb : d73644 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d69422, d73644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69422, d73644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69423 q = 1) (hb : d73645 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d69423, d73645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69423, d73645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69424 q = 1) (hb : d73646 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d69424, d73646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69424, d73646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69425 q = 1) (hb : d73647 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d69425, d73647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69425, d73647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69426 q = 1) (hb : d73648 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d69426, d73648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69426, d73648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5669 (p : Pattern) (ha : d69432 p = 1) (hb : d73654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69427 q = 1) (hb : d73649 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d69427, d73649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5668 q ha hb
    | true =>
      simp only [d69427, d73649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69428 q = 1) (hb : d73650 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d69428, d73650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69428, d73650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69429 q = 1) (hb : d73651 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d69429, d73651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69429, d73651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69430 q = 1) (hb : d73652 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d69430, d73652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69430, d73652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69431 q = 1) (hb : d73653 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d69431, d73653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69431, d73653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69432 q = 1) (hb : d73654 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d69432, d73654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69432, d73654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5670 (p : Pattern) (ha : d61692 p = 1) (hb : d73495 p = 1) : d73658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d73494 q = 1) : d73507 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d73494, d73507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4204 q ha hb
    | true =>
      simp only [d3343, d73494, d73507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3344 q = 1) (hb : d73495 q = 1) : d73508 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d73495, d73508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d73495, d73508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d61689 q = 1) (hb : d73495 q = 1) : d73655 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61689, d73655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61689, d73655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61690 q = 1) (hb : d73495 q = 1) : d73656 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61690, d73656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61690, d73656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61691 q = 1) (hb : d73495 q = 1) : d73657 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61691, d73657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61691, d73657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61692 q = 1) (hb : d73495 q = 1) : d73658 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61692, d73658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61692, d73658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5671 (p : Pattern) (ha : d61698 p = 1) (hb : d73495 p = 1) : d73664 p = 1 := by
  have h0 (q : Pattern) (ha : d61688 q = 1) (hb : d73495 q = 1) : d61688 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61693 q = 1) (hb : d73495 q = 1) : d73659 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61693, d73659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61693, d73659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5670 q ha hb
  have h3 (q : Pattern) (ha : d61694 q = 1) (hb : d73495 q = 1) : d73660 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61694, d73660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61694, d73660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61695 q = 1) (hb : d73495 q = 1) : d73661 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61695, d73661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61695, d73661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61696 q = 1) (hb : d73495 q = 1) : d73662 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61696, d73662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61696, d73662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61697 q = 1) (hb : d73495 q = 1) : d73663 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61697, d73663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61697, d73663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61698 q = 1) (hb : d73495 q = 1) : d73664 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61698, d73664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61698, d73664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5672 (p : Pattern) (ha : d61702 p = 1) (hb : d73495 p = 1) : d73668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d73494 q = 1) : d73522 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d73494, d73522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4212 q ha hb
    | true =>
      simp only [d3359, d73494, d73522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3360 q = 1) (hb : d73495 q = 1) : d73523 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d73495, d73523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d73495, d73523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d61699 q = 1) (hb : d73495 q = 1) : d73665 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61699, d73665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61699, d73665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61700 q = 1) (hb : d73495 q = 1) : d73666 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61700, d73666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61700, d73666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61701 q = 1) (hb : d73495 q = 1) : d73667 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61701, d73667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61701, d73667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61702 q = 1) (hb : d73495 q = 1) : d73668 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61702, d73668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61702, d73668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5673 (p : Pattern) (ha : d61708 p = 1) (hb : d73495 p = 1) : d73674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61703 q = 1) (hb : d73495 q = 1) : d73669 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61703, d73669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61703, d73669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5672 q ha hb
  have h2 (q : Pattern) (ha : d61704 q = 1) (hb : d73495 q = 1) : d73670 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61704, d73670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61704, d73670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61705 q = 1) (hb : d73495 q = 1) : d73671 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61705, d73671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61705, d73671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61706 q = 1) (hb : d73495 q = 1) : d73672 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61706, d73672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61706, d73672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61707 q = 1) (hb : d73495 q = 1) : d73673 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61707, d73673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61707, d73673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61708 q = 1) (hb : d73495 q = 1) : d73674 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61708, d73674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61708, d73674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5674 (p : Pattern) (ha : d61713 p = 1) (hb : d73495 p = 1) : d73679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d73494 q = 1) : d73538 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d73494, d73538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4220 q ha hb
    | true =>
      simp only [d3376, d73494, d73538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3377 q = 1) (hb : d73495 q = 1) : d73539 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d73495, d73539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d73495, d73539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d61710 q = 1) (hb : d73495 q = 1) : d73676 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61710, d73676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61710, d73676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61711 q = 1) (hb : d73495 q = 1) : d73677 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61711, d73677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61711, d73677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61712 q = 1) (hb : d73495 q = 1) : d73678 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61712, d73678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61712, d73678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61713 q = 1) (hb : d73495 q = 1) : d73679 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61713, d73679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61713, d73679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5675 (p : Pattern) (ha : d61719 p = 1) (hb : d73495 p = 1) : d73685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61714 q = 1) (hb : d73495 q = 1) : d73680 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61714, d73680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61714, d73680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5674 q ha hb
  have h2 (q : Pattern) (ha : d61715 q = 1) (hb : d73495 q = 1) : d73681 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61715, d73681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61715, d73681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61716 q = 1) (hb : d73495 q = 1) : d73682 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61716, d73682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61716, d73682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61717 q = 1) (hb : d73495 q = 1) : d73683 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61717, d73683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61717, d73683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61718 q = 1) (hb : d73495 q = 1) : d73684 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61718, d73684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61718, d73684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61719 q = 1) (hb : d73495 q = 1) : d73685 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61719, d73685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61719, d73685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5676 (p : Pattern) (ha : d61725 p = 1) (hb : d73495 p = 1) : d73691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d73494 q = 1) : d73555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d73494, d73555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4228 q ha hb
    | true =>
      simp only [d3394, d73494, d73555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3395 q = 1) (hb : d73495 q = 1) : d73556 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d73495, d73556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d73495, d73556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d61722 q = 1) (hb : d73495 q = 1) : d73688 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61722, d73688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61722, d73688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61723 q = 1) (hb : d73495 q = 1) : d73689 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61723, d73689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61723, d73689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61724 q = 1) (hb : d73495 q = 1) : d73690 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61724, d73690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61724, d73690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61725 q = 1) (hb : d73495 q = 1) : d73691 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61725, d73691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61725, d73691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5677 (p : Pattern) (ha : d61731 p = 1) (hb : d73495 p = 1) : d73697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61726 q = 1) (hb : d73495 q = 1) : d73692 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61726, d73692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61726, d73692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5676 q ha hb
  have h2 (q : Pattern) (ha : d61727 q = 1) (hb : d73495 q = 1) : d73693 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61727, d73693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61727, d73693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61728 q = 1) (hb : d73495 q = 1) : d73694 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61728, d73694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61728, d73694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61729 q = 1) (hb : d73495 q = 1) : d73695 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61729, d73695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61729, d73695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61730 q = 1) (hb : d73495 q = 1) : d73696 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61730, d73696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61730, d73696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61731 q = 1) (hb : d73495 q = 1) : d73697 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61731, d73697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61731, d73697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5678 (p : Pattern) (ha : d61738 p = 1) (hb : d73495 p = 1) : d73704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d73494 q = 1) : d73573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d73494, d73573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4236 q ha hb
    | true =>
      simp only [d3413, d73494, d73573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3414 q = 1) (hb : d73495 q = 1) : d73574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d73495, d73574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d73495, d73574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d61735 q = 1) (hb : d73495 q = 1) : d73701 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61735, d73701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61735, d73701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61736 q = 1) (hb : d73495 q = 1) : d73702 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61736, d73702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61736, d73702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61737 q = 1) (hb : d73495 q = 1) : d73703 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61737, d73703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61737, d73703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61738 q = 1) (hb : d73495 q = 1) : d73704 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61738, d73704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61738, d73704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5679 (p : Pattern) (ha : d61744 p = 1) (hb : d73495 p = 1) : d73710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61739 q = 1) (hb : d73495 q = 1) : d73705 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61739, d73705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61739, d73705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5678 q ha hb
  have h2 (q : Pattern) (ha : d61740 q = 1) (hb : d73495 q = 1) : d73706 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61740, d73706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61740, d73706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61741 q = 1) (hb : d73495 q = 1) : d73707 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61741, d73707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61741, d73707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61742 q = 1) (hb : d73495 q = 1) : d73708 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61742, d73708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61742, d73708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61743 q = 1) (hb : d73495 q = 1) : d73709 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61743, d73709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61743, d73709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61744 q = 1) (hb : d73495 q = 1) : d73710 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61744, d73710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61744, d73710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5680 (p : Pattern) (ha : d61752 p = 1) (hb : d73495 p = 1) : d73718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d73494 q = 1) : d73592 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d73494, d73592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4244 q ha hb
    | true =>
      simp only [d3433, d73494, d73592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3434 q = 1) (hb : d73495 q = 1) : d73593 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d73495, d73593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d73495, d73593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d61749 q = 1) (hb : d73495 q = 1) : d73715 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61749, d73715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61749, d73715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61750 q = 1) (hb : d73495 q = 1) : d73716 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61750, d73716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61750, d73716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61751 q = 1) (hb : d73495 q = 1) : d73717 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61751, d73717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61751, d73717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61752 q = 1) (hb : d73495 q = 1) : d73718 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61752, d73718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61752, d73718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5681 (p : Pattern) (ha : d61758 p = 1) (hb : d73495 p = 1) : d73724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61753 q = 1) (hb : d73495 q = 1) : d73719 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61753, d73719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61753, d73719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5680 q ha hb
  have h2 (q : Pattern) (ha : d61754 q = 1) (hb : d73495 q = 1) : d73720 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61754, d73720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61754, d73720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61755 q = 1) (hb : d73495 q = 1) : d73721 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61755, d73721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61755, d73721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61756 q = 1) (hb : d73495 q = 1) : d73722 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61756, d73722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61756, d73722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61757 q = 1) (hb : d73495 q = 1) : d73723 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61757, d73723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61757, d73723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61758 q = 1) (hb : d73495 q = 1) : d73724 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61758, d73724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61758, d73724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5682 (p : Pattern) (ha : d61764 p = 1) (hb : d73495 p = 1) : d73730 p = 1 := by
  have h0 (q : Pattern) (ha : d61709 q = 1) (hb : d73495 q = 1) : d73675 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61709, d73675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5671 q ha hb
    | true =>
      simp only [d61709, d73675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5673 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61720 q = 1) (hb : d73495 q = 1) : d73686 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61720, d73686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61720, d73686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5675 q ha hb
  have h3 (q : Pattern) (ha : d61721 q = 1) (hb : d73495 q = 1) : d73687 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61721, d73687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61721, d73687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61732 q = 1) (hb : d73495 q = 1) : d73698 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61732, d73698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61732, d73698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5677 q ha hb
  have h5 (q : Pattern) (ha : d61733 q = 1) (hb : d73495 q = 1) : d73699 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61733, d73699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61733, d73699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61734 q = 1) (hb : d73495 q = 1) : d73700 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61734, d73700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61734, d73700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61745 q = 1) (hb : d73495 q = 1) : d73711 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61745, d73711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61745, d73711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5679 q ha hb
  have h8 (q : Pattern) (ha : d61746 q = 1) (hb : d73495 q = 1) : d73712 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61746, d73712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61746, d73712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61747 q = 1) (hb : d73495 q = 1) : d73713 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61747, d73713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61747, d73713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61748 q = 1) (hb : d73495 q = 1) : d73714 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61748, d73714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61748, d73714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61759 q = 1) (hb : d73495 q = 1) : d73725 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61759, d73725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61759, d73725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5681 q ha hb
  have h12 (q : Pattern) (ha : d61760 q = 1) (hb : d73495 q = 1) : d73726 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61760, d73726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61760, d73726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61761 q = 1) (hb : d73495 q = 1) : d73727 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61761, d73727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61761, d73727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61762 q = 1) (hb : d73495 q = 1) : d73728 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61762, d73728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61762, d73728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61763 q = 1) (hb : d73495 q = 1) : d73729 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61763, d73729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61763, d73729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61764 q = 1) (hb : d73495 q = 1) : d73730 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61764, d73730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61764, d73730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5683 (p : Pattern) (ha : d61770 p = 1) (hb : d73495 p = 1) : d73736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61765 q = 1) (hb : d73495 q = 1) : d73731 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61765, d73731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5682 q ha hb
    | true =>
      simp only [d61765, d73731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61766 q = 1) (hb : d73495 q = 1) : d73732 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61766, d73732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61766, d73732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61767 q = 1) (hb : d73495 q = 1) : d73733 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61767, d73733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61767, d73733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61768 q = 1) (hb : d73495 q = 1) : d73734 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61768, d73734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61768, d73734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61769 q = 1) (hb : d73495 q = 1) : d73735 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61769, d73735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61769, d73735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61770 q = 1) (hb : d73495 q = 1) : d73736 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61770, d73736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61770, d73736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5684 (p : Pattern) (ha : d61776 p = 1) (hb : d73495 p = 1) : d73742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61771 q = 1) (hb : d73495 q = 1) : d73737 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61771, d73737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5683 q ha hb
    | true =>
      simp only [d61771, d73737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61772 q = 1) (hb : d73495 q = 1) : d73738 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61772, d73738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61772, d73738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61773 q = 1) (hb : d73495 q = 1) : d73739 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61773, d73739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61773, d73739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61774 q = 1) (hb : d73495 q = 1) : d73740 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61774, d73740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61774, d73740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61775 q = 1) (hb : d73495 q = 1) : d73741 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61775, d73741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61775, d73741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61776 q = 1) (hb : d73495 q = 1) : d73742 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61776, d73742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61776, d73742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5685 (p : Pattern) (ha : d61782 p = 1) (hb : d73495 p = 1) : d73748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61777 q = 1) (hb : d73495 q = 1) : d73743 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61777, d73743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5684 q ha hb
    | true =>
      simp only [d61777, d73743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61778 q = 1) (hb : d73495 q = 1) : d73744 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61778, d73744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61778, d73744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61779 q = 1) (hb : d73495 q = 1) : d73745 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61779, d73745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61779, d73745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61780 q = 1) (hb : d73495 q = 1) : d73746 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61780, d73746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61780, d73746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61781 q = 1) (hb : d73495 q = 1) : d73747 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61781, d73747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61781, d73747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61782 q = 1) (hb : d73495 q = 1) : d73748 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61782, d73748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61782, d73748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5686 (p : Pattern) (ha : d61788 p = 1) (hb : d73495 p = 1) : d73754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61783 q = 1) (hb : d73495 q = 1) : d73749 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61783, d73749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5685 q ha hb
    | true =>
      simp only [d61783, d73749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61784 q = 1) (hb : d73495 q = 1) : d73750 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61784, d73750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61784, d73750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61785 q = 1) (hb : d73495 q = 1) : d73751 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61785, d73751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61785, d73751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61786 q = 1) (hb : d73495 q = 1) : d73752 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61786, d73752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61786, d73752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61787 q = 1) (hb : d73495 q = 1) : d73753 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61787, d73753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61787, d73753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61788 q = 1) (hb : d73495 q = 1) : d73754 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61788, d73754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61788, d73754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5687 (p : Pattern) (ha : d61794 p = 1) (hb : d73495 p = 1) : d73760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61789 q = 1) (hb : d73495 q = 1) : d73755 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61789, d73755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5686 q ha hb
    | true =>
      simp only [d61789, d73755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61790 q = 1) (hb : d73495 q = 1) : d73756 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61790, d73756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61790, d73756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61791 q = 1) (hb : d73495 q = 1) : d73757 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61791, d73757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61791, d73757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61792 q = 1) (hb : d73495 q = 1) : d73758 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61792, d73758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61792, d73758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61793 q = 1) (hb : d73495 q = 1) : d73759 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61793, d73759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61793, d73759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61794 q = 1) (hb : d73495 q = 1) : d73760 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61794, d73760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61794, d73760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5688 (p : Pattern) (ha : d61800 p = 1) (hb : d73495 p = 1) : d73766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61795 q = 1) (hb : d73495 q = 1) : d73761 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61795, d73761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5687 q ha hb
    | true =>
      simp only [d61795, d73761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61796 q = 1) (hb : d73495 q = 1) : d73762 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61796, d73762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61796, d73762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61797 q = 1) (hb : d73495 q = 1) : d73763 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61797, d73763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61797, d73763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61798 q = 1) (hb : d73495 q = 1) : d73764 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61798, d73764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61798, d73764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61799 q = 1) (hb : d73495 q = 1) : d73765 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61799, d73765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61799, d73765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61800 q = 1) (hb : d73495 q = 1) : d73766 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61800, d73766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61800, d73766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5689 (p : Pattern) (ha : d61806 p = 1) (hb : d73495 p = 1) : d73772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61801 q = 1) (hb : d73495 q = 1) : d73767 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61801, d73767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5688 q ha hb
    | true =>
      simp only [d61801, d73767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61802 q = 1) (hb : d73495 q = 1) : d73768 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61802, d73768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61802, d73768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61803 q = 1) (hb : d73495 q = 1) : d73769 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61803, d73769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61803, d73769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61804 q = 1) (hb : d73495 q = 1) : d73770 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61804, d73770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61804, d73770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61805 q = 1) (hb : d73495 q = 1) : d73771 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61805, d73771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61805, d73771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61806 q = 1) (hb : d73495 q = 1) : d73772 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61806, d73772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61806, d73772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5690 (p : Pattern) (ha : d61683 p = 1) (hb : d68784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d68762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d68762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4353 q ha hb
    | true =>
      simp only [d3329, d68762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d68763 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d68763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d68763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d61680 q = 1) (hb : d68764 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61680, d68764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61680, d68764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61681 q = 1) (hb : d68765 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61681, d68765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61681, d68765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d68772 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d61682 q = 1) (hb : d68773 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61682, d68773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61682, d68773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d68783 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d61683 q = 1) (hb : d68784 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61683, d68784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61683, d68784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro5691 (p : Pattern) (ha : d68865 p = 1) (hb : d73658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68804 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68830 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d68831 q = 1) (hb : d73507 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68831, d73507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4358 q hb ha
    | true =>
      simp only [d68831, d73507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d68842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d68843 q = 1) (hb : d73508 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68843, d73508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68843, d73508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d68844 q = 1) (hb : d73655 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68844, d73655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68844, d73655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68845 q = 1) (hb : d73656 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68845, d73656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68845, d73656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d68852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d68853 q = 1) (hb : d73657 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68853, d73657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68853, d73657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d68864 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d68865 q = 1) (hb : d73658 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68865, d73658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68865, d73658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5692 (p : Pattern) (ha : d68871 p = 1) (hb : d73664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61684 q = 1) (hb : d68785 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61684, d68785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61684, d68785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5690 q ha hb
  have h3 (q : Pattern) (ha : d61685 q = 1) (hb : d68786 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61685, d68786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61685, d68786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61686 q = 1) (hb : d68787 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61686, d68787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61686, d68787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61687 q = 1) (hb : d68788 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61687, d68788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61687, d68788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61688 q = 1) (hb : d68789 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61688, d68789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61688, d68789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68866 q = 1) (hb : d73659 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68866, d73659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68866, d73659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5691 q ha hb
  have h8 (q : Pattern) (ha : d68867 q = 1) (hb : d73660 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68867, d73660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68867, d73660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68868 q = 1) (hb : d73661 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68868, d73661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68868, d73661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68869 q = 1) (hb : d73662 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68869, d73662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68869, d73662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68870 q = 1) (hb : d73663 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68870, d73663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68870, d73663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d68871 q = 1) (hb : d73664 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68871, d73664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d68871, d73664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5693 (p : Pattern) (ha : d68956 p = 1) (hb : d73668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68886 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68912 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d68913 q = 1) (hb : d73522 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68913, d73522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4364 q hb ha
    | true =>
      simp only [d68913, d73522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d68933 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d68934 q = 1) (hb : d73523 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68934, d73523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68934, d73523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d68935 q = 1) (hb : d73665 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68935, d73665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68935, d73665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68936 q = 1) (hb : d73666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68936, d73666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68936, d73666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d68943 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d68944 q = 1) (hb : d73667 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68944, d73667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68944, d73667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d68955 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d68956 q = 1) (hb : d73668 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68956, d73668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68956, d73668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5694 (p : Pattern) (ha : d68962 p = 1) (hb : d73674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68957 q = 1) (hb : d73669 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68957, d73669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68957, d73669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5693 q ha hb
  have h2 (q : Pattern) (ha : d68958 q = 1) (hb : d73670 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68958, d73670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68958, d73670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68959 q = 1) (hb : d73671 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68959, d73671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68959, d73671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68960 q = 1) (hb : d73672 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68960, d73672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68960, d73672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68961 q = 1) (hb : d73673 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68961, d73673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68961, d73673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68962 q = 1) (hb : d73674 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68962, d73674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68962, d73674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5695 (p : Pattern) (ha : d69048 p = 1) (hb : d73679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69004 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69005 q = 1) (hb : d73538 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69005, d73538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4370 q hb ha
    | true =>
      simp only [d69005, d73538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d69025 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69026 q = 1) (hb : d73539 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69026, d73539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69026, d73539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69027 q = 1) (hb : d73676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69027, d73676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69027, d73676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69028 q = 1) (hb : d73677 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69028, d73677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69028, d73677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d69035 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69036 q = 1) (hb : d73678 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69036, d73678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69036, d73678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d69047 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d69048 q = 1) (hb : d73679 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69048, d73679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69048, d73679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5696 (p : Pattern) (ha : d69054 p = 1) (hb : d73685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69049 q = 1) (hb : d73680 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69049, d73680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69049, d73680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5695 q ha hb
  have h2 (q : Pattern) (ha : d69050 q = 1) (hb : d73681 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69050, d73681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69050, d73681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69051 q = 1) (hb : d73682 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69051, d73682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69051, d73682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69052 q = 1) (hb : d73683 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69052, d73683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69052, d73683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69053 q = 1) (hb : d73684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69053, d73684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69053, d73684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69054 q = 1) (hb : d73685 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69054, d73685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69054, d73685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5697 (p : Pattern) (ha : d69155 p = 1) (hb : d73691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69071 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69097 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69098 q = 1) (hb : d73555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69098, d73555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4376 q hb ha
    | true =>
      simp only [d69098, d73555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d69132 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69133 q = 1) (hb : d73556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69133, d73556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69133, d73556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69134 q = 1) (hb : d73688 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69134, d73688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69134, d73688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69135 q = 1) (hb : d73689 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69135, d73689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69135, d73689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d69142 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69143 q = 1) (hb : d73690 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69143, d73690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69143, d73690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d69154 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d69155 q = 1) (hb : d73691 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69155, d73691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69155, d73691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5698 (p : Pattern) (ha : d69161 p = 1) (hb : d73697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69156 q = 1) (hb : d73692 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69156, d73692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69156, d73692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5697 q ha hb
  have h2 (q : Pattern) (ha : d69157 q = 1) (hb : d73693 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69157, d73693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69157, d73693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69158 q = 1) (hb : d73694 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69158, d73694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69158, d73694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69159 q = 1) (hb : d73695 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69159, d73695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69159, d73695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69160 q = 1) (hb : d73696 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69160, d73696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69160, d73696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69161 q = 1) (hb : d73697 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69161, d73697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69161, d73697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5699 (p : Pattern) (ha : d69268 p = 1) (hb : d73704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69179 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69205 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69206 q = 1) (hb : d73573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69206, d73573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4382 q hb ha
    | true =>
      simp only [d69206, d73573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d69245 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69246 q = 1) (hb : d73574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69246, d73574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69246, d73574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69247 q = 1) (hb : d73701 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69247, d73701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69247, d73701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69248 q = 1) (hb : d73702 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69248, d73702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69248, d73702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d69255 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69256 q = 1) (hb : d73703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69256, d73703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69256, d73703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d69267 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d69268 q = 1) (hb : d73704 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69268, d73704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69268, d73704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5700 (p : Pattern) (ha : d69274 p = 1) (hb : d73710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69269 q = 1) (hb : d73705 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69269, d73705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69269, d73705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5699 q ha hb
  have h2 (q : Pattern) (ha : d69270 q = 1) (hb : d73706 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69270, d73706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69270, d73706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69271 q = 1) (hb : d73707 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69271, d73707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69271, d73707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69272 q = 1) (hb : d73708 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69272, d73708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69272, d73708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69273 q = 1) (hb : d73709 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69273, d73709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69273, d73709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69274 q = 1) (hb : d73710 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69274, d73710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69274, d73710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5701 (p : Pattern) (ha : d69378 p = 1) (hb : d73718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69293 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69320 q = 1) (hb : d73592 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69320, d73592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4388 q hb ha
    | true =>
      simp only [d69320, d73592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d69355 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69356 q = 1) (hb : d73593 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69356, d73593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69356, d73593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69357 q = 1) (hb : d73715 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69357, d73715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69357, d73715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69358 q = 1) (hb : d73716 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69358, d73716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69358, d73716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d69365 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69366 q = 1) (hb : d73717 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69366, d73717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69366, d73717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d69377 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d69378 q = 1) (hb : d73718 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69378, d73718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69378, d73718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5702 (p : Pattern) (ha : d69384 p = 1) (hb : d73724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69379 q = 1) (hb : d73719 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69379, d73719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69379, d73719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5701 q ha hb
  have h2 (q : Pattern) (ha : d69380 q = 1) (hb : d73720 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69380, d73720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69380, d73720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69381 q = 1) (hb : d73721 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69381, d73721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69381, d73721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69382 q = 1) (hb : d73722 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69382, d73722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69382, d73722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69383 q = 1) (hb : d73723 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69383, d73723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69383, d73723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69384 q = 1) (hb : d73724 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69384, d73724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69384, d73724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5703 (p : Pattern) (ha : d69390 p = 1) (hb : d73730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d68963 q = 1) (hb : d73675 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68963, d73675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5692 q ha hb
    | true =>
      simp only [d68963, d73675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5694 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69055 q = 1) (hb : d73686 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69055, d73686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69055, d73686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5696 q ha hb
  have h3 (q : Pattern) (ha : d69056 q = 1) (hb : d73687 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69056, d73687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69056, d73687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69162 q = 1) (hb : d73698 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69162, d73698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69162, d73698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5698 q ha hb
  have h5 (q : Pattern) (ha : d69163 q = 1) (hb : d73699 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69163, d73699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69163, d73699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69164 q = 1) (hb : d73700 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69164, d73700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69164, d73700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69275 q = 1) (hb : d73711 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69275, d73711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69275, d73711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5700 q ha hb
  have h8 (q : Pattern) (ha : d69276 q = 1) (hb : d73712 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69276, d73712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69276, d73712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69277 q = 1) (hb : d73713 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69277, d73713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69277, d73713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69278 q = 1) (hb : d73714 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69278, d73714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69278, d73714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69385 q = 1) (hb : d73725 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69385, d73725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69385, d73725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5702 q ha hb
  have h12 (q : Pattern) (ha : d69386 q = 1) (hb : d73726 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69386, d73726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69386, d73726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69387 q = 1) (hb : d73727 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69387, d73727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69387, d73727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69388 q = 1) (hb : d73728 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69388, d73728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69388, d73728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69389 q = 1) (hb : d73729 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d69389, d73729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69389, d73729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69390 q = 1) (hb : d73730 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d69390, d73730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69390, d73730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5704 (p : Pattern) (ha : d69396 p = 1) (hb : d73736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69391 q = 1) (hb : d73731 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d69391, d73731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5703 q ha hb
    | true =>
      simp only [d69391, d73731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69392 q = 1) (hb : d73732 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d69392, d73732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69392, d73732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69393 q = 1) (hb : d73733 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d69393, d73733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69393, d73733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69394 q = 1) (hb : d73734 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d69394, d73734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69394, d73734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69395 q = 1) (hb : d73735 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d69395, d73735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69395, d73735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69396 q = 1) (hb : d73736 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d69396, d73736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69396, d73736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5705 (p : Pattern) (ha : d69402 p = 1) (hb : d73742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69397 q = 1) (hb : d73737 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d69397, d73737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5704 q ha hb
    | true =>
      simp only [d69397, d73737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69398 q = 1) (hb : d73738 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d69398, d73738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69398, d73738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69399 q = 1) (hb : d73739 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d69399, d73739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69399, d73739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69400 q = 1) (hb : d73740 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d69400, d73740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69400, d73740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69401 q = 1) (hb : d73741 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d69401, d73741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69401, d73741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69402 q = 1) (hb : d73742 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d69402, d73742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69402, d73742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5706 (p : Pattern) (ha : d69408 p = 1) (hb : d73748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69403 q = 1) (hb : d73743 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d69403, d73743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5705 q ha hb
    | true =>
      simp only [d69403, d73743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69404 q = 1) (hb : d73744 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d69404, d73744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69404, d73744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69405 q = 1) (hb : d73745 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d69405, d73745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69405, d73745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69406 q = 1) (hb : d73746 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d69406, d73746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69406, d73746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69407 q = 1) (hb : d73747 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d69407, d73747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69407, d73747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69408 q = 1) (hb : d73748 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d69408, d73748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69408, d73748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5707 (p : Pattern) (ha : d69414 p = 1) (hb : d73754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69409 q = 1) (hb : d73749 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d69409, d73749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5706 q ha hb
    | true =>
      simp only [d69409, d73749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69410 q = 1) (hb : d73750 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d69410, d73750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69410, d73750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69411 q = 1) (hb : d73751 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d69411, d73751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69411, d73751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69412 q = 1) (hb : d73752 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d69412, d73752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69412, d73752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69413 q = 1) (hb : d73753 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d69413, d73753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69413, d73753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69414 q = 1) (hb : d73754 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d69414, d73754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69414, d73754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5708 (p : Pattern) (ha : d69420 p = 1) (hb : d73760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69415 q = 1) (hb : d73755 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d69415, d73755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5707 q ha hb
    | true =>
      simp only [d69415, d73755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69416 q = 1) (hb : d73756 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d69416, d73756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69416, d73756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69417 q = 1) (hb : d73757 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d69417, d73757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69417, d73757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69418 q = 1) (hb : d73758 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d69418, d73758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69418, d73758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69419 q = 1) (hb : d73759 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d69419, d73759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69419, d73759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69420 q = 1) (hb : d73760 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d69420, d73760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69420, d73760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5709 (p : Pattern) (ha : d69426 p = 1) (hb : d73766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69421 q = 1) (hb : d73761 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d69421, d73761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5708 q ha hb
    | true =>
      simp only [d69421, d73761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69422 q = 1) (hb : d73762 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d69422, d73762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69422, d73762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69423 q = 1) (hb : d73763 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d69423, d73763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69423, d73763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69424 q = 1) (hb : d73764 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d69424, d73764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69424, d73764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69425 q = 1) (hb : d73765 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d69425, d73765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69425, d73765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69426 q = 1) (hb : d73766 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d69426, d73766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69426, d73766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5710 (p : Pattern) (ha : d69432 p = 1) (hb : d73772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69427 q = 1) (hb : d73767 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d69427, d73767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5709 q ha hb
    | true =>
      simp only [d69427, d73767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69428 q = 1) (hb : d73768 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d69428, d73768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69428, d73768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69429 q = 1) (hb : d73769 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d69429, d73769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69429, d73769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69430 q = 1) (hb : d73770 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d69430, d73770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69430, d73770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69431 q = 1) (hb : d73771 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d69431, d73771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69431, d73771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69432 q = 1) (hb : d73772 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d69432, d73772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69432, d73772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5711 (p : Pattern) (ha : d61683 p = 1) (hb : d69972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69440 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d69441 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d69441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4402 q ha hb
    | true =>
      simp only [d3329, d69441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d69968 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d69968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d69968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d61680 q = 1) (hb : d69969 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61680, d69969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61680, d69969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61681 q = 1) (hb : d69970 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61681, d69970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61681, d69970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d69451 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d61682 q = 1) (hb : d69971 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61682, d69971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61682, d69971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d69461 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d61683 q = 1) (hb : d69972 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61683, d69972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61683, d69972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro5712 (p : Pattern) (ha : d69989 p = 1) (hb : d73658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d4703 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69477 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69478 q = 1) (hb : d73507 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69478, d73507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4407 q hb ha
    | true =>
      simp only [d69478, d73507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4743 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69978 q = 1) (hb : d73508 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69978, d73508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69978, d73508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69979 q = 1) (hb : d73655 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69979, d73655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69979, d73655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69980 q = 1) (hb : d73656 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69980, d73656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69980, d73656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d69983 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69984 q = 1) (hb : d73657 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69984, d73657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69984, d73657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d69988 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d69989 q = 1) (hb : d73658 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69989, d73658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69989, d73658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5713 (p : Pattern) (ha : d69995 p = 1) (hb : d73664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61684 q = 1) (hb : d69973 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61684, d69973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61684, d69973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5711 q ha hb
  have h3 (q : Pattern) (ha : d61685 q = 1) (hb : d69974 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61685, d69974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61685, d69974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61686 q = 1) (hb : d69975 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61686, d69975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61686, d69975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61687 q = 1) (hb : d69976 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61687, d69976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61687, d69976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61688 q = 1) (hb : d69977 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61688, d69977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61688, d69977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69990 q = 1) (hb : d73659 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69990, d73659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69990, d73659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5712 q ha hb
  have h8 (q : Pattern) (ha : d69991 q = 1) (hb : d73660 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69991, d73660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69991, d73660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69992 q = 1) (hb : d73661 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69992, d73661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69992, d73661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69993 q = 1) (hb : d73662 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69993, d73662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69993, d73662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69994 q = 1) (hb : d73663 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69994, d73663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69994, d73663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69995 q = 1) (hb : d73664 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69995, d73664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d69995, d73664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5714 (p : Pattern) (ha : d70007 p = 1) (hb : d73668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d4788 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69516 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69517 q = 1) (hb : d73522 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69517, d73522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4413 q hb ha
    | true =>
      simp only [d69517, d73522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4837 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69996 q = 1) (hb : d73523 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69996, d73523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69996, d73523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69997 q = 1) (hb : d73665 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69997, d73665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69997, d73665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69998 q = 1) (hb : d73666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69998, d73666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69998, d73666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d70001 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d70002 q = 1) (hb : d73667 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70002, d73667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70002, d73667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70006 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70007 q = 1) (hb : d73668 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70007, d73668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70007, d73668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5715 (p : Pattern) (ha : d70013 p = 1) (hb : d73674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70008 q = 1) (hb : d73669 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70008, d73669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70008, d73669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5714 q ha hb
  have h2 (q : Pattern) (ha : d70009 q = 1) (hb : d73670 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70009, d73670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70009, d73670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70010 q = 1) (hb : d73671 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70010, d73671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70010, d73671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70011 q = 1) (hb : d73672 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70011, d73672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70011, d73672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70012 q = 1) (hb : d73673 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70012, d73673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70012, d73673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70013 q = 1) (hb : d73674 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70013, d73674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70013, d73674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5716 (p : Pattern) (ha : d70026 p = 1) (hb : d73679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d4883 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69557 q = 1) (hb : d73538 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69557, d73538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4419 q hb ha
    | true =>
      simp only [d69557, d73538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4932 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70015 q = 1) (hb : d73539 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70015, d73539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70015, d73539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d70016 q = 1) (hb : d73676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70016, d73676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70016, d73676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70017 q = 1) (hb : d73677 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70017, d73677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70017, d73677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d70020 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d70021 q = 1) (hb : d73678 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70021, d73678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70021, d73678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70025 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70026 q = 1) (hb : d73679 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70026, d73679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70026, d73679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5717 (p : Pattern) (ha : d70032 p = 1) (hb : d73685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70027 q = 1) (hb : d73680 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70027, d73680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70027, d73680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5716 q ha hb
  have h2 (q : Pattern) (ha : d70028 q = 1) (hb : d73681 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70028, d73681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70028, d73681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70029 q = 1) (hb : d73682 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70029, d73682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70029, d73682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70030 q = 1) (hb : d73683 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70030, d73683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70030, d73683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70031 q = 1) (hb : d73684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70031, d73684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70031, d73684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70032 q = 1) (hb : d73685 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70032, d73685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70032, d73685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5718 (p : Pattern) (ha : d70046 p = 1) (hb : d73691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d4979 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69597 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69598 q = 1) (hb : d73555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69598, d73555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4425 q hb ha
    | true =>
      simp only [d69598, d73555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5042 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70035 q = 1) (hb : d73556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70035, d73556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70035, d73556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d70036 q = 1) (hb : d73688 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70036, d73688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70036, d73688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70037 q = 1) (hb : d73689 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70037, d73689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70037, d73689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d70040 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d70041 q = 1) (hb : d73690 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70041, d73690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70041, d73690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70045 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70046 q = 1) (hb : d73691 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70046, d73691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70046, d73691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5719 (p : Pattern) (ha : d70052 p = 1) (hb : d73697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70047 q = 1) (hb : d73692 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70047, d73692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70047, d73692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5718 q ha hb
  have h2 (q : Pattern) (ha : d70048 q = 1) (hb : d73693 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70048, d73693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70048, d73693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70049 q = 1) (hb : d73694 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70049, d73694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70049, d73694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70050 q = 1) (hb : d73695 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70050, d73695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70050, d73695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70051 q = 1) (hb : d73696 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70051, d73696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70051, d73696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70052 q = 1) (hb : d73697 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70052, d73697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70052, d73697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5720 (p : Pattern) (ha : d70067 p = 1) (hb : d73704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5090 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69639 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69640 q = 1) (hb : d73573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69640, d73573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4431 q hb ha
    | true =>
      simp only [d69640, d73573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5158 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70056 q = 1) (hb : d73574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70056, d73574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70056, d73574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d70057 q = 1) (hb : d73701 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70057, d73701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70057, d73701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70058 q = 1) (hb : d73702 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70058, d73702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70058, d73702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d70061 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d70062 q = 1) (hb : d73703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70062, d73703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70062, d73703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70066 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70067 q = 1) (hb : d73704 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70067, d73704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70067, d73704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5721 (p : Pattern) (ha : d70073 p = 1) (hb : d73710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70068 q = 1) (hb : d73705 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70068, d73705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70068, d73705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5720 q ha hb
  have h2 (q : Pattern) (ha : d70069 q = 1) (hb : d73706 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70069, d73706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70069, d73706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70070 q = 1) (hb : d73707 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70070, d73707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70070, d73707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70071 q = 1) (hb : d73708 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70071, d73708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70071, d73708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70072 q = 1) (hb : d73709 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70072, d73709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70072, d73709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70073 q = 1) (hb : d73710 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70073, d73710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70073, d73710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5722 (p : Pattern) (ha : d70089 p = 1) (hb : d73718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5207 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69682 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69683 q = 1) (hb : d73592 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69683, d73592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4437 q hb ha
    | true =>
      simp only [d69683, d73592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5271 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70078 q = 1) (hb : d73593 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70078, d73593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70078, d73593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d70079 q = 1) (hb : d73715 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70079, d73715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70079, d73715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70080 q = 1) (hb : d73716 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70080, d73716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70080, d73716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d70083 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d70084 q = 1) (hb : d73717 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70084, d73717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70084, d73717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70088 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70089 q = 1) (hb : d73718 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70089, d73718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70089, d73718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro5723 (p : Pattern) (ha : d70095 p = 1) (hb : d73724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70090 q = 1) (hb : d73719 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70090, d73719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70090, d73719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5722 q ha hb
  have h2 (q : Pattern) (ha : d70091 q = 1) (hb : d73720 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70091, d73720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70091, d73720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70092 q = 1) (hb : d73721 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70092, d73721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70092, d73721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70093 q = 1) (hb : d73722 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70093, d73722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70093, d73722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70094 q = 1) (hb : d73723 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70094, d73723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70094, d73723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70095 q = 1) (hb : d73724 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70095, d73724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70095, d73724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5724 (p : Pattern) (ha : d70101 p = 1) (hb : d73730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d70014 q = 1) (hb : d73675 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70014, d73675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5713 q ha hb
    | true =>
      simp only [d70014, d73675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5715 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70033 q = 1) (hb : d73686 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70033, d73686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70033, d73686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5717 q ha hb
  have h3 (q : Pattern) (ha : d70034 q = 1) (hb : d73687 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70034, d73687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70034, d73687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70053 q = 1) (hb : d73698 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70053, d73698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70053, d73698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5719 q ha hb
  have h5 (q : Pattern) (ha : d70054 q = 1) (hb : d73699 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70054, d73699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70054, d73699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70055 q = 1) (hb : d73700 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70055, d73700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70055, d73700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70074 q = 1) (hb : d73711 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70074, d73711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70074, d73711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5721 q ha hb
  have h8 (q : Pattern) (ha : d70075 q = 1) (hb : d73712 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70075, d73712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70075, d73712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70076 q = 1) (hb : d73713 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70076, d73713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70076, d73713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70077 q = 1) (hb : d73714 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d70077, d73714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70077, d73714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d70096 q = 1) (hb : d73725 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70096, d73725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70096, d73725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5723 q ha hb
  have h12 (q : Pattern) (ha : d70097 q = 1) (hb : d73726 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70097, d73726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70097, d73726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d70098 q = 1) (hb : d73727 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70098, d73727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70098, d73727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70099 q = 1) (hb : d73728 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d70099, d73728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70099, d73728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70100 q = 1) (hb : d73729 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d70100, d73729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70100, d73729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70101 q = 1) (hb : d73730 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d70101, d73730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70101, d73730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5725 (p : Pattern) (ha : d70107 p = 1) (hb : d73736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70102 q = 1) (hb : d73731 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d70102, d73731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5724 q ha hb
    | true =>
      simp only [d70102, d73731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70103 q = 1) (hb : d73732 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d70103, d73732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70103, d73732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70104 q = 1) (hb : d73733 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d70104, d73733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70104, d73733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70105 q = 1) (hb : d73734 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d70105, d73734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70105, d73734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70106 q = 1) (hb : d73735 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d70106, d73735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70106, d73735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70107 q = 1) (hb : d73736 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d70107, d73736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70107, d73736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5726 (p : Pattern) (ha : d70113 p = 1) (hb : d73742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70108 q = 1) (hb : d73737 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d70108, d73737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5725 q ha hb
    | true =>
      simp only [d70108, d73737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70109 q = 1) (hb : d73738 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d70109, d73738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70109, d73738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70110 q = 1) (hb : d73739 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d70110, d73739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70110, d73739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70111 q = 1) (hb : d73740 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d70111, d73740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70111, d73740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70112 q = 1) (hb : d73741 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d70112, d73741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70112, d73741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70113 q = 1) (hb : d73742 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d70113, d73742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70113, d73742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5727 (p : Pattern) (ha : d70119 p = 1) (hb : d73748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70114 q = 1) (hb : d73743 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d70114, d73743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5726 q ha hb
    | true =>
      simp only [d70114, d73743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70115 q = 1) (hb : d73744 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d70115, d73744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70115, d73744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70116 q = 1) (hb : d73745 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d70116, d73745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70116, d73745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70117 q = 1) (hb : d73746 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d70117, d73746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70117, d73746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70118 q = 1) (hb : d73747 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d70118, d73747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70118, d73747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70119 q = 1) (hb : d73748 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d70119, d73748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70119, d73748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5728 (p : Pattern) (ha : d70125 p = 1) (hb : d73754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70120 q = 1) (hb : d73749 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d70120, d73749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5727 q ha hb
    | true =>
      simp only [d70120, d73749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70121 q = 1) (hb : d73750 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d70121, d73750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70121, d73750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70122 q = 1) (hb : d73751 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d70122, d73751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70122, d73751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70123 q = 1) (hb : d73752 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d70123, d73752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70123, d73752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70124 q = 1) (hb : d73753 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d70124, d73753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70124, d73753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70125 q = 1) (hb : d73754 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d70125, d73754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70125, d73754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5729 (p : Pattern) (ha : d70131 p = 1) (hb : d73760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70126 q = 1) (hb : d73755 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d70126, d73755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5728 q ha hb
    | true =>
      simp only [d70126, d73755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70127 q = 1) (hb : d73756 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d70127, d73756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70127, d73756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70128 q = 1) (hb : d73757 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d70128, d73757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70128, d73757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70129 q = 1) (hb : d73758 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d70129, d73758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70129, d73758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70130 q = 1) (hb : d73759 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d70130, d73759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70130, d73759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70131 q = 1) (hb : d73760 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d70131, d73760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70131, d73760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5730 (p : Pattern) (ha : d70137 p = 1) (hb : d73766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70132 q = 1) (hb : d73761 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d70132, d73761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5729 q ha hb
    | true =>
      simp only [d70132, d73761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70133 q = 1) (hb : d73762 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d70133, d73762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70133, d73762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70134 q = 1) (hb : d73763 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d70134, d73763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70134, d73763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70135 q = 1) (hb : d73764 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d70135, d73764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70135, d73764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70136 q = 1) (hb : d73765 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d70136, d73765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70136, d73765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70137 q = 1) (hb : d73766 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d70137, d73766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70137, d73766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5731 (p : Pattern) (ha : d70143 p = 1) (hb : d73772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70138 q = 1) (hb : d73767 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d70138, d73767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5730 q ha hb
    | true =>
      simp only [d70138, d73767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70139 q = 1) (hb : d73768 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d70139, d73768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70139, d73768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70140 q = 1) (hb : d73769 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d70140, d73769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70140, d73769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70141 q = 1) (hb : d73770 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d70141, d73770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70141, d73770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70142 q = 1) (hb : d73771 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d70142, d73771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70142, d73771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70143 q = 1) (hb : d73772 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d70143, d73772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70143, d73772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5732 (p : Pattern) (ha : d62701 p = 1) (hb : d62934 p = 1) : d62701 p = 1 := by
  have h0 (q : Pattern) (ha : d62701 q = 1) (hb : d62934 q = 1) : d62701 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro5733 (p : Pattern) (ha : d3497 p = 1) (hb : d51907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d51897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, d51897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, d51897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d51898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, d51898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, d51898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d51899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, d51899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, d51899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51906 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3497 q = 1) (hb : d51907 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3497, d51907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3497, d51907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5734 (p : Pattern) (ha : d3503 p = 1) (hb : d54633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51900 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3498 q = 1) (hb : d51908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3498, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3498, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5733 q ha hb
  have h3 (q : Pattern) (ha : d3499 q = 1) (hb : d51909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3499, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3499, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3500 q = 1) (hb : d51910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3500, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3500, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3501 q = 1) (hb : d51911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3501, d51911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3501, d51911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3502 q = 1) (hb : d54632 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3502, d54632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3502, d54632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d3503 q = 1) (hb : d54633 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3503, d54633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3503, d54633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5735 (p : Pattern) (ha : d213 p = 1) (hb : d51963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d51952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d51953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d51954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51962 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d213 q = 1) (hb : d51963 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, d51963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, d51963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5736 (p : Pattern) (ha : d52029 p = 1) (hb : d62554 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4335 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
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
  have h13 (q : Pattern) (ha : d4336 q = 1) (hb : d52010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d52010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4336, d52010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51641 q = 1) (hb : d52011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51642 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52028 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52029 q = 1) (hb : d62554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52029, d62554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d52029, d62554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro5737 (p : Pattern) (ha : d54639 p = 1) (hb : d62560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2525 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5735 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2526 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2526, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3508 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3508, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3508, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52013 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52030 q = 1) (hb : d62555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52030, d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5736 q ha hb
  have h8 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d52033 q = 1) (hb : d62556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d62556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52033, d62556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52034 q = 1) (hb : d62557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d62557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52034, d62557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52035 q = 1) (hb : d62558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d62558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d62558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54638 q = 1) (hb : d62559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54638, d62559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54638, d62559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d54639 q = 1) (hb : d62560 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54639, d62560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54639, d62560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h13 p ha hb
theorem andIntro5738 (p : Pattern) (ha : d2536 p = 1) (hb : d52090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52089 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2536 q = 1) (hb : d52090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2536, d52090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2536, d52090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5739 (p : Pattern) (ha : d2536 p = 1) (hb : d52163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2536 q = 1) (hb : d52163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2536, d52163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2536, d52163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5740 (p : Pattern) (ha : d52161 p = 1) (hb : d62566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51 q ha hb
    | true =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52 q ha hb
    | true =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d337 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4371 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d370 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d371 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4372 q = 1) (hb : d52140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d52140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4372, d52140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51658 q = 1) (hb : d52141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51658, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51659 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51659, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52160 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52161 q = 1) (hb : d62566 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52161, d62566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d52161, d62566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro5741 (p : Pattern) (ha : d54646 p = 1) (hb : d62572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52083 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2537 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5738 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2538 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2538, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3521 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3521, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3521, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52143 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52162 q = 1) (hb : d62567 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52162, d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52162, d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5740 q ha hb
  have h8 (q : Pattern) (ha : d3524 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3524, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5739 q ha hb
    | true =>
      simp only [d3524, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5735 q ha hb
  have h9 (q : Pattern) (ha : d52165 q = 1) (hb : d62568 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52165, d62568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52165, d62568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52166 q = 1) (hb : d62569 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d62569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52166, d62569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52167 q = 1) (hb : d62570 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d62570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52167, d62570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54645 q = 1) (hb : d62571 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54645, d62571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54645, d62571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d54646 q = 1) (hb : d62572 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54646, d62572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54646, d62572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h13 p ha hb
theorem andIntro5742 (p : Pattern) (ha : d54652 p = 1) (hb : d62578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3504 q = 1) (hb : d54634 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3504, d54634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3504, d54634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5734 q ha hb
  have h2 (q : Pattern) (ha : d3505 q = 1) (hb : d54635 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3505, d54635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3505, d54635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3506 q = 1) (hb : d54636 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3506, d54636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3506, d54636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3507 q = 1) (hb : d54637 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3507, d54637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3507, d54637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54640 q = 1) (hb : d62561 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54640, d62561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54640, d62561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5737 q ha hb
  have h6 (q : Pattern) (ha : d54641 q = 1) (hb : d62562 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54641, d62562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54641, d62562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54642 q = 1) (hb : d62563 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54642, d62563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54642, d62563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54643 q = 1) (hb : d62564 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54643, d62564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54643, d62564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54644 q = 1) (hb : d62565 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54644, d62565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d54644, d62565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54647 q = 1) (hb : d62573 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54647, d62573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54647, d62573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5741 q ha hb
  have h11 (q : Pattern) (ha : d54648 q = 1) (hb : d62574 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54648, d62574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54648, d62574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54649 q = 1) (hb : d62575 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54649, d62575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54649, d62575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54650 q = 1) (hb : d62576 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54650, d62576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54650, d62576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54651 q = 1) (hb : d62577 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54651, d62577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54651, d62577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54652 q = 1) (hb : d62578 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54652, d62578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54652, d62578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5743 (p : Pattern) (ha : d2549 p = 1) (hb : d52254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d492 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d493 q = 1) (hb : d52240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d52241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d494, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d52242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d52243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52253 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2549 q = 1) (hb : d52254 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2549, d52254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2549, d52254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5744 (p : Pattern) (ha : d2549 p = 1) (hb : d52342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d492 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d493 q = 1) (hb : d52240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d52241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d494, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d52242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d52243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2549 q = 1) (hb : d52342 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2549, d52342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2549, d52342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5745 (p : Pattern) (ha : d3539 p = 1) (hb : d52348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
    | true =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52347 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3539 q = 1) (hb : d52348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3539, d52348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3539, d52348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5746 (p : Pattern) (ha : d52335 p = 1) (hb : d62579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d515 q = 1) (hb : d52262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87 q ha hb
    | true =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q ha hb
  have h2 (q : Pattern) (ha : d516 q = 1) (hb : d52263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d517 q = 1) (hb : d52264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d518 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d525 q = 1) (hb : d52272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89 q ha hb
    | true =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h6 (q : Pattern) (ha : d526 q = 1) (hb : d52273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d527 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d561 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4408 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4408, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d603 q = 1) (hb : d52310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d604 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4409 q = 1) (hb : d52312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d52312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4409, d52312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51683 q = 1) (hb : d52313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51683, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51684 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51684, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52334 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52335 q = 1) (hb : d62579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52335, d62579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d52335, d62579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro5747 (p : Pattern) (ha : d54654 p = 1) (hb : d62585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52244 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2550 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5743 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2551 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2551, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3536 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3536, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3536, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52315 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52336 q = 1) (hb : d62580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52336, d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52336, d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5746 q ha hb
  have h8 (q : Pattern) (ha : d3540 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3540, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5744 q ha hb
    | true =>
      simp only [d3540, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5745 q ha hb
  have h9 (q : Pattern) (ha : d52350 q = 1) (hb : d62581 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52350, d62581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52350, d62581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52351 q = 1) (hb : d62582 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d62582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52351, d62582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52352 q = 1) (hb : d62583 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d62583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52352, d62583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54653 q = 1) (hb : d62584 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54653, d62584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54653, d62584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d54654 q = 1) (hb : d62585 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54654, d62585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54654, d62585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h13 p ha hb
theorem andIntro5748 (p : Pattern) (ha : d54660 p = 1) (hb : d62591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54655 q = 1) (hb : d62586 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54655, d62586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54655, d62586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5747 q ha hb
  have h2 (q : Pattern) (ha : d54656 q = 1) (hb : d62587 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54656, d62587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54656, d62587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54657 q = 1) (hb : d62588 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54657, d62588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54657, d62588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54658 q = 1) (hb : d62589 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54658, d62589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54658, d62589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54659 q = 1) (hb : d62590 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54659, d62590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54659, d62590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54660 q = 1) (hb : d62591 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54660, d62591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54660, d62591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5749 (p : Pattern) (ha : d2563 p = 1) (hb : d52476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d784 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d785 q = 1) (hb : d52462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d52463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d786, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d52464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d52465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52475 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2563 q = 1) (hb : d52476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2563, d52476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2563, d52476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
end NetHack.Soko22Hazard87
